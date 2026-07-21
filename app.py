#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Meraki MX L3 防火墙规则导出/导入 Web 工具

功能：
1. 导出某 network 的 MX L3 防火墙规则到网页可编辑表格（含对象引用解析）
2. 网页表格直接编辑后导入到新站点（支持 CSV 下载/上传）
3. Policy Object 双向转换：
   - 导出端：按需逐个单查被引用的对象 id（不全量拉取）
   - 导入端：全量拉取目标 org 对象建多键索引（支持按名称/实际值/组名匹配），带本地缓存
4. 自动处理模板绑定站点：绑定模板的 network 读写目标切换为 configTemplateId

启动：python app.py → 浏览器访问 http://localhost:5000
"""

import os
import re
import io
import csv
import json
import time
import uuid
import zipfile
import threading
from typing import List, Dict, Optional, Tuple, Set, Any
from datetime import datetime

import requests
from flask import Flask, request, jsonify, render_template, Response
from dotenv import load_dotenv

# 加载 .env 配置
load_dotenv()

# ---------------------------------------------------------------------------
# 全局配置
# ---------------------------------------------------------------------------
BASE_URL = os.environ.get("MERAKI_BASE_URL", "https://api.meraki.cn/api/v1").rstrip("/")
API_KEY = os.environ.get("MERAKI_API_KEY", "")
FLASK_PORT = int(os.environ.get("FLASK_PORT", "5000"))

# 对象引用格式（经真实环境验证）：
#   OBJ(id)   -> 单个 Policy Object
#   GRP(id)   -> Policy Object Group（对象组）
#   VLAN(id).port -> VLAN 引用（CIDR 字面写法，导入时原样保留，不转对象）
OBJ_REF_PATTERN = re.compile(r"^(OBJ|GRP)\((\d+)\)$")
OBJ_PREFIX = "OBJ"
GRP_PREFIX = "GRP"

# VLAN 引用格式（导出端 GET 返回的就是这种）：
#   VLAN(<tag>)        -> 引用某 VLAN 的子网
#   VLAN(<tag>).port   -> 引用某 VLAN 的某端口范围（如 VLAN(1102).*）
# 导入端必须把 VLAN(tag) 映射成目标网络实际的子网 CIDR，
# 裸 VLAN 引用无法直接被 L3 防火墙 PUT 接受（API 会判非法 cidr）。
VLAN_REF_PATTERN = re.compile(r"^VLAN\((\d+)\)(\..*)?$")


def classify_ref_segment(seg: str) -> Tuple[str, str]:
    """
    判断一段 cidr 值是对象引用还是字面值。
    返回 (类型, id)：
      ('obj', id)   -> 单个对象
      ('grp', id)   -> 对象组
      ('literal', seg) -> 字面值（含 VLAN(id).x、IP、Any 等）
    """
    m = OBJ_REF_PATTERN.match(seg.strip())
    if m:
        kind = "obj" if m.group(1) == OBJ_PREFIX else "grp"
        return kind, m.group(2)
    return "literal", seg.strip()


def classify_vlan_ref(seg: str) -> Optional[Tuple[str, str]]:
    """
    判断一段 cidr 是否为 VLAN 引用。
    返回 (tag, suffix) 或 None：
      VLAN(1102)        -> ("1102", "")
      VLAN(1102).*      -> ("1102", ".*")
      其他              -> None（非 VLAN 引用）
    """
    m = VLAN_REF_PATTERN.match(seg.strip())
    if m:
        return m.group(1), m.group(2) or ""
    return None

# 缓存目录
CACHE_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "cache")
os.makedirs(CACHE_DIR, exist_ok=True)

# 回滚索引文件：记录每一批导入/合并操作的备份，供一键倒回使用
ROLLBACK_INDEX = os.path.join(CACHE_DIR, "rollback_index.json")
ROLLBACK_MAX_BATCHES = 50  # 索引最多保留的批次数，超出裁剪最旧
_rollback_lock = threading.Lock()


def _load_rollback_index() -> Dict:
    """读取回滚索引（{"batches": [...]}），文件不存在/损坏时返回空结构。"""
    if not os.path.exists(ROLLBACK_INDEX):
        return {"batches": []}
    try:
        with open(ROLLBACK_INDEX, "r", encoding="utf-8") as f:
            data = json.load(f)
        if not isinstance(data, dict) or not isinstance(data.get("batches"), list):
            return {"batches": []}
        return data
    except Exception as e:
        print(f"  [rollback] 索引读取失败，重置: {e}")
        return {"batches": []}


def _save_rollback_index(idx: Dict) -> None:
    """写盘回滚索引，仅保留最近 ROLLBACK_MAX_BATCHES 个批次（裁剪最旧）。"""
    batches = idx.get("batches", [])
    if len(batches) > ROLLBACK_MAX_BATCHES:
        idx["batches"] = batches[-ROLLBACK_MAX_BATCHES:]
    try:
        with open(ROLLBACK_INDEX, "w", encoding="utf-8") as f:
            json.dump(idx, f, ensure_ascii=False, indent=2)
    except Exception as e:
        print(f"  [rollback] 索引写盘失败: {e}")


def _record_rollback_batch(op_type: str, sites: List[Dict]) -> str:
    """记录一批可倒回操作。
    op_type: 'merge' | 'full_import'
    sites: [{network_id, target_id, network_name, org_id, backup_file, syslog_default}]
    返回 batch_id。无可倒回站点时不记录，返回空串。"""
    if not sites:
        return ""
    batch_id = datetime.now().strftime("%Y%m%d_%H%M%S") + "_" + uuid.uuid4().hex[:4]
    entry = {
        "batch_id": batch_id,
        "op_type": op_type,
        "created_at": datetime.now().isoformat(),
        "sites": sites,
    }
    with _rollback_lock:
        idx = _load_rollback_index()
        idx["batches"].append(entry)
        _save_rollback_index(idx)
    return batch_id


# ===========================================================================
# Meraki API 客户端
# ===========================================================================
class MerakiL3FirewallApp:
    """Meraki L3 防火墙规则管理器 + Flask 应用"""

    def __init__(self):
        if not API_KEY:
            raise ValueError(
                "未配置 MERAKI_API_KEY，请在 .env 文件中填入（参考 .env.example）"
            )
        self.session = requests.Session()
        self.session.headers.update({
            "X-Cisco-Meraki-API-Key": API_KEY,
            "Content-Type": "application/json",
        })
        self.request_delay = 0.1
        self._delay_lock = threading.Lock()
        self._last_request_time = 0.0

        # 进程内对象索引缓存：{org_id: {"built_at": ts, "index": {...}}}
        self._index_cache: Dict[str, Dict] = {}
        self._index_lock = threading.Lock()

    # ------------------------------------------------------------------
    # 底层请求（复用现有脚本风格：限速 + 429 重试 + 指数退避）
    # ------------------------------------------------------------------
    def _throttle(self):
        """请求间隔控制（线程安全）"""
        with self._delay_lock:
            now = time.time()
            wait = self.request_delay - (now - self._last_request_time)
            if wait > 0:
                time.sleep(wait)
            self._last_request_time = time.time()

    def _make_request(self, method: str, endpoint: str,
                      params: Optional[Dict] = None,
                      payload: Optional[Dict] = None) -> Any:
        """发送 API 请求（带限速、429 重试、3 次指数退避）"""
        url = f"{BASE_URL}{endpoint}"
        max_retries = 3
        for attempt in range(max_retries):
            self._throttle()
            try:
                resp = self.session.request(
                    method, url, params=params, json=payload, timeout=30
                )
                if resp.status_code == 429:
                    retry_after = int(resp.headers.get("Retry-After", 1))
                    print(f"  [429] 触发限流，等待 {retry_after}s 后重试...")
                    time.sleep(retry_after)
                    continue
                resp.raise_for_status()
                if resp.status_code == 204:
                    return {"success": True}
                return resp.json()
            except requests.exceptions.RequestException as e:
                if attempt < max_retries - 1 and not hasattr(e, "response"):
                    time.sleep(2 ** attempt)
                    continue
                msg = f"API请求失败: {method} {url}\n错误: {e}"
                if hasattr(e, "response") and e.response is not None:
                    msg += f"\n响应: {e.response.text}"
                raise RuntimeError(msg) from e
        raise RuntimeError(f"请求超出重试次数: {method} {url}")

    def _raw_get(self, endpoint: str, params: Optional[Dict] = None):
        """发送 GET 并返回 response 对象（用于分页取 Link header）"""
        url = f"{BASE_URL}{endpoint}"
        max_retries = 3
        for attempt in range(max_retries):
            self._throttle()
            try:
                resp = self.session.get(url, params=params, timeout=30)
                if resp.status_code == 429:
                    retry_after = int(resp.headers.get("Retry-After", 1))
                    print(f"  [429] 触发限流，等待 {retry_after}s 后重试...")
                    time.sleep(retry_after)
                    continue
                resp.raise_for_status()
                return resp
            except requests.exceptions.RequestException as e:
                if attempt < max_retries - 1:
                    time.sleep(2 ** attempt)
                    continue
                msg = f"API请求失败: GET {url}\n错误: {e}"
                if hasattr(e, "response") and e.response is not None:
                    msg += f"\n响应: {e.response.text}"
                raise RuntimeError(msg) from e
        raise RuntimeError(f"请求超出重试次数: GET {url}")

    def _get_all_pages(self, endpoint: str, params: Optional[Dict] = None) -> List[Dict]:
        """获取所有分页数据（解析 Link header 的 startingAfter 游标）。
        params 里的 perPage 若已指定则保留，否则默认 1000。"""
        all_results: List[Dict] = []
        page_params = dict(params or {})
        page_params.setdefault("perPage", 1000)
        per_page = page_params["perPage"]
        while True:
            resp = self._raw_get(endpoint, page_params)
            data = resp.json()
            if isinstance(data, list):
                all_results.extend(data)
                if len(data) < per_page:
                    break
                link_header = resp.headers.get("Link", "")
                if 'rel="next"' not in link_header:
                    break
                m = re.search(r"startingAfter=([^&>]+)", link_header)
                if m:
                    page_params["startingAfter"] = m.group(1)
                else:
                    break
            else:
                return data  # 非列表，直接返回
        return all_results

    # ------------------------------------------------------------------
    # 组织 / 网络 / 模板
    # ------------------------------------------------------------------
    def get_organizations(self) -> List[Dict]:
        return self._make_request("GET", "/organizations")

    def get_organization_networks(self, org_id: str) -> List[Dict]:
        return self._get_all_pages(f"/organizations/{org_id}/networks")

    def get_network(self, network_id: str) -> Dict:
        return self._make_request("GET", f"/networks/{network_id}")

    def get_organization_config_templates(self, org_id: str) -> List[Dict]:
        """获取组织下的配置模板列表（用于展示模板名）"""
        return self._get_all_pages(f"/organizations/{org_id}/configTemplates")

    def resolve_target_id(self, network_id: str, org_id: str = "") -> Dict:
        """
        判断目标是普通网络、绑定模板的网络，还是模板本身，返回真正用于读写 L3 防火墙的目标 id。

        三种情况:
          - 模板本身（network_id 是模板 id）: target_id = 该模板 id，is_template=True
          - 绑定模板的普通网络: target_id = configTemplateId
          - 普通网络: target_id = network_id

        返回:
            {
              "network_id": 原始,
              "target_id": 实际读写目标,
              "bound_to_template": bool,      # 绑定模板的网络（不含模板本身）
              "is_template": bool,            # 传入的 id 本身是模板
              "config_template_id": str|None,
              "config_template_name": str|None,
              "bound_network_count": int|None,
              "network_name": str,
            }
        """
        # 先尝试 getNetwork：成功说明是普通网络
        net = None
        try:
            net = self.get_network(network_id)
        except RuntimeError as e:
            # 404 通常意味着是模板 id（getNetwork 查不到模板）
            net = None

        # 情况1: getNetwork 失败 → 可能是模板，查模板列表确认
        if net is None:
            return self._resolve_as_template(network_id, org_id)

        # 普通网络
        bound = net.get("isBoundToConfigTemplate", False)
        result = {
            "network_id": network_id,
            "target_id": network_id,
            "bound_to_template": bound,
            "is_template": False,
            "config_template_id": net.get("configTemplateId"),
            "config_template_name": None,
            "bound_network_count": None,
            "network_name": net.get("name", ""),
        }
        if bound and net.get("configTemplateId"):
            tmpl_id = net["configTemplateId"]
            result["target_id"] = tmpl_id
            try:
                oid = org_id or net.get("organizationId") or self._org_of_network(network_id)
                if oid:
                    templates = self.get_organization_config_templates(oid)
                    for t in templates:
                        if t.get("id") == tmpl_id:
                            result["config_template_name"] = t.get("name")
                            break
                    bound_nets = self._get_all_pages(
                        f"/organizations/{oid}/networks",
                        {"configTemplateId": tmpl_id},
                    )
                    result["bound_network_count"] = len(bound_nets)
            except Exception as e:
                print(f"  [warn] 获取模板信息失败: {e}")
        return result

    def _resolve_as_template(self, template_id: str, org_id: str = "") -> Dict:
        """把 template_id 当模板处理（getNetwork 查不到时调用）"""
        tmpl_name = ""
        bound_count = None
        try:
            if org_id:
                templates = self.get_organization_config_templates(org_id)
                for t in templates:
                    if t.get("id") == template_id:
                        tmpl_name = t.get("name", "")
                        break
                # 绑定该模板的网络数
                bound_nets = self._get_all_pages(
                    f"/organizations/{org_id}/networks",
                    {"configTemplateId": template_id},
                )
                bound_count = len(bound_nets)
        except Exception as e:
            print(f"  [warn] 模板信息获取失败: {e}")
        return {
            "network_id": template_id,
            "target_id": template_id,
            "bound_to_template": False,
            "is_template": True,
            "config_template_id": template_id,
            "config_template_name": tmpl_name,
            "bound_network_count": bound_count,
            "network_name": tmpl_name,
        }

    def _org_of_network(self, network_id: str) -> Optional[str]:
        """从 network 详情取 organizationId"""
        try:
            net = self.get_network(network_id)
            return net.get("organizationId")
        except Exception:
            return None

    # ------------------------------------------------------------------
    # L3 防火墙规则
    # ------------------------------------------------------------------
    def get_l3_rules(self, target_id: str) -> Dict:
        """获取 L3 规则（target_id 可能是 network_id 或 template_id）"""
        data = self._make_request(
            "GET", f"/networks/{target_id}/appliance/firewall/l3FirewallRules"
        )
        return data if isinstance(data, dict) else {"rules": data}

    def write_backup(self, network_id: str, raw_rules: Dict) -> str:
        """将目标站点当前规则（含 rules + syslogDefaultRule）写入备份文件，返回绝对路径。
        文件名沿用 backup_<network_id>_<时间戳>.json，写盘失败不抛异常（返回空串）。"""
        backup_ts = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
        backup_file = os.path.join(CACHE_DIR, f"backup_{network_id}_{backup_ts}.json")
        try:
            with open(backup_file, "w", encoding="utf-8") as f:
                json.dump(raw_rules, f, ensure_ascii=False, indent=2)
            return backup_file
        except Exception as e:
            print(f"  [warn] {network_id} 备份写入失败: {e}")
            return ""

    def update_l3_rules(self, target_id: str, rules: List[Dict],
                        syslog_default_rule: bool,
                        allowed_vlans: Optional[Set[str]] = None,
                        patch_offset: Optional[int] = None,
                        patch_len: int = 0) -> Dict:
        """更新 L3 规则（整体覆盖）。
        PUT 前先做本地格式校验：任何残留的非法 cidr 都会在这里抛出可读的
        RuntimeError，而不是让 API 返回难定位的 400。
        allowed_vlans: 目标 MX 上已存在的 VLAN tag 集合；其中的 VLAN 引用放行
        （增量合并场景：目标规则自身的 VLAN 引用、补丁透传的同号 VLAN 都合法）。
        不传则所有裸 VLAN 都被拒绝（全量导入新站点场景）。
        patch_offset/patch_len: 增量合并时补丁在 rules 列表中的起始位置与长度，
        用于报错信息区分「补丁规则」与「目标现有规则」，方便定位问题来源。"""
        problems = validate_l3_rules(rules, allowed_vlans)
        if problems:
            detail = "\n".join(
                f"  - 规则#{p['index']+1} {p['field']}: {p['value']}"
                + _problem_origin_tag(p['index'], patch_offset, patch_len, allowed_vlans)
                for p in problems[:20]
            )
            if len(problems) > 20:
                detail += f"\n  - ...（另有 {len(problems)-20} 处）"
            raise RuntimeError(
                f"导入校验失败，发现 {len(problems)} 处非法 cidr 段"
                f"（VLAN 引用需在该 MX 上存在，或先映射成子网）:\n{detail}"
            )
        payload = {"rules": rules, "syslogDefaultRule": syslog_default_rule}
        return self._make_request(
            "PUT",
            f"/networks/{target_id}/appliance/firewall/l3FirewallRules",
            payload=payload,
        )

    # ------------------------------------------------------------------
    # VLAN：导入端读取目标网络 VLAN，建 tag->子网 映射
    # ------------------------------------------------------------------
    def get_appliance_vlans(self, target_id: str) -> List[Dict]:
        """获取目标（network_id 或 template_id）的 VLAN 列表。
        VLAN 未启用 / 非 appliance / 模板读取失败时返回空列表并打 warn，
        不抛异常（调用方据此把含 VLAN 引用的规则转入决策面板）。"""
        try:
            data = self._make_request(
                "GET", f"/networks/{target_id}/appliance/vlans"
            )
            return data if isinstance(data, list) else []
        except RuntimeError as e:
            print(f"  [warn] 读取 VLAN 列表失败（可能未启用 VLAN）: {e}")
            return []

    def build_vlan_map(self, target_id: str) -> Dict[str, str]:
        """构建 {vlan_tag: subnet_cidr}，跳过 id=='0'（WAN）。
        仅含有子网的 VLAN（全量导入「VLAN→子网」映射用）。
        注意：模板的 unique 型 VLAN（subnet=None）不会出现在此 map 中，
        但它们在规则里仍是合法引用 → 判断 VLAN 是否存在请用 get_appliance_vlan_tags。"""
        vlans = self.get_appliance_vlans(target_id)
        vlan_map: Dict[str, str] = {}
        for v in vlans:
            tag = str(v.get("id", ""))
            subnet = v.get("subnet", "")
            if tag and tag != "0" and subnet:
                vlan_map[tag] = subnet
        return vlan_map

    def get_appliance_vlan_tags(self, target_id: str) -> Set[str]:
        """返回目标 MX 上存在的所有 VLAN tag 集合（含 subnet 为空的）。
        用于校验「VLAN(tag) 引用在该 MX 上是否存在」——与子网无关。
        跳过 id=='0'（WAN）。"""
        vlans = self.get_appliance_vlans(target_id)
        tags: Set[str] = set()
        for v in vlans:
            tag = str(v.get("id", ""))
            if tag and tag != "0":
                tags.add(tag)
        return tags

    # ------------------------------------------------------------------
    # Policy Object：导入端全量建索引 + 本地缓存
    # ------------------------------------------------------------------
    def get_all_policy_objects(self, org_id: str) -> List[Dict]:
        return self._get_all_pages(
            f"/organizations/{org_id}/policyObjects", {"perPage": 5000}
        )

    def get_all_policy_groups(self, org_id: str) -> List[Dict]:
        return self._get_all_pages(
            f"/organizations/{org_id}/policyObjects/groups", {"perPage": 1000}
        )

    def create_policy_object(self, org_id: str, payload: Dict) -> Dict:
        return self._make_request(
            "POST", f"/organizations/{org_id}/policyObjects", payload=payload
        )

    def create_policy_group(self, org_id: str, payload: Dict) -> Dict:
        return self._make_request(
            "POST", f"/organizations/{org_id}/policyObjects/groups", payload=payload
        )

    def build_object_index(self, org_id: str, force_refresh: bool = False) -> Dict:
        """
        全量拉取目标 org 的对象+组，构建多键索引（导入端匹配用）。
        带本地文件缓存，避免重复全量拉取。

        索引结构:
            {
              "objects_by_id": {id -> {name,type,category,value}},
              "name_to_id": {name -> id},          # 用户写对象名时映射
              "value_to_id": {value -> id},        # 实际值匹配（跨站点自动重映射）
              "groups_by_id": {gid -> {name,objectIds,expanded_value}},
              "group_name_to_id": {gname -> gid},
              "object_count": int, "group_count": int,
              "built_at": ts, "cached": bool
            }
        """
        # 进程内缓存
        with self._index_lock:
            cached = self._index_cache.get(org_id)

        cache_file = os.path.join(CACHE_DIR, f"{org_id}_objects.json")

        # 尝试文件缓存
        if not force_refresh and cached is None and os.path.exists(cache_file):
            try:
                with open(cache_file, "r", encoding="utf-8") as f:
                    cached = json.load(f)
                print(f"  [import] 命中文件缓存: {cache_file}")
            except Exception:
                cached = None

        if cached is not None and not force_refresh:
            # 缓存校验：拉一小页（perPage=10）比对总数 + 最新更新时间
            # X-Total-Count header 在 Meraki 上不稳定，改用总数比对 + updatedAt 哨兵
            try:
                sample = self._raw_get(
                    f"/organizations/{org_id}/policyObjects", {"perPage": 10}
                ).json()
                # 比对对象总数（用样本无法精确判断总数，所以同时检查
                # 缓存里记录的对象 id 集合是否覆盖了样本里的对象）
                cached_ids = set(cached.get("objects_by_id", {}).keys())
                sample_ids = {str(o.get("id")) for o in sample}
                if sample_ids and sample_ids.issubset(cached_ids):
                    # 样本里的对象都在缓存中 → 缓存仍然有效
                    with self._index_lock:
                        self._index_cache[org_id] = cached
                    cached["cached"] = True
                    print(f"  [import] 缓存有效（样本对象均命中缓存）")
                    return cached
                else:
                    print(f"  [import] 缓存失效（样本对象未全部命中），重新拉取")
            except Exception as e:
                print(f"  [import] 缓存校验失败，重新拉取: {e}")

        # 全量拉取
        print(f"  [import] 全量拉取 org {org_id} 的对象+组（建索引）")
        objects = self.get_all_policy_objects(org_id)
        groups = self.get_all_policy_groups(org_id)

        index = self._compose_index(objects, groups)
        index["built_at"] = datetime.now().isoformat()
        index["cached"] = False

        # 写文件缓存
        try:
            with open(cache_file, "w", encoding="utf-8") as f:
                json.dump(index, f, ensure_ascii=False, indent=2)
        except Exception as e:
            print(f"  [import] 写缓存失败: {e}")

        with self._index_lock:
            self._index_cache[org_id] = index
        return index

    @staticmethod
    def _object_value(obj: Dict) -> str:
        """从对象取实际值（按 type 承载字段）"""
        for k in ("cidr", "fqdn", "ip"):
            v = obj.get(k)
            if v:
                return str(v)
        return ""

    def _compose_index(self, objects: List[Dict], groups: List[Dict]) -> Dict:
        """从全量对象/组列表构建多键索引"""
        objects_by_id: Dict[str, Dict] = {}
        name_to_id: Dict[str, str] = {}
        value_to_id: Dict[str, str] = {}

        for obj in objects:
            oid = str(obj.get("id"))
            value = self._object_value(obj)
            entry = {
                "name": obj.get("name", ""),
                "type": obj.get("type", ""),
                "category": obj.get("category", ""),
                "value": value,
            }
            objects_by_id[oid] = entry
            if obj.get("name"):
                name_to_id[obj["name"]] = oid
            if value:
                value_to_id[value] = oid

        groups_by_id: Dict[str, Dict] = {}
        group_name_to_id: Dict[str, str] = {}
        for g in groups:
            gid = str(g.get("id"))
            member_ids = [str(x) for x in g.get("objectIds", [])]
            # 展开组成员的实际值
            expanded = []
            for mid in member_ids:
                if mid in objects_by_id:
                    expanded.append(objects_by_id[mid]["value"])
            groups_by_id[gid] = {
                "name": g.get("name", ""),
                "objectIds": member_ids,
                "expanded_value": ";".join(expanded),
            }
            if g.get("name"):
                group_name_to_id[g["name"]] = gid

        return {
            "objects_by_id": objects_by_id,
            "name_to_id": name_to_id,
            "value_to_id": value_to_id,
            "groups_by_id": groups_by_id,
            "group_name_to_id": group_name_to_id,
            "object_count": len(objects),
            "group_count": len(groups),
        }


# ===========================================================================
# 核心转换逻辑
# ===========================================================================
def split_cidr_segments(cidr_str: str) -> List[str]:
    """把 cidr 字段按逗号拆分成多段（处理 OBJ_ID 与字面值混合）"""
    if not cidr_str:
        return []
    return [s.strip() for s in str(cidr_str).split(",") if s.strip()]


def extract_obj_ids(rules: List[Dict]) -> Tuple[Set[str], Set[str]]:
    """
    从规则里提取所有被引用的对象 id 和组 id（区分类型）。
    返回 (obj_ids, group_ids)。
    VLAN(id).x 视为字面值不收集。
    """
    obj_ids: Set[str] = set()
    group_ids: Set[str] = set()
    for rule in rules:
        for field in ("srcCidr", "destCidr"):
            for seg in split_cidr_segments(rule.get(field, "")):
                kind, oid = classify_ref_segment(seg)
                if kind == "obj":
                    obj_ids.add(oid)
                elif kind == "grp":
                    group_ids.add(oid)
    return obj_ids, group_ids


def select_referenced_from_index(
    index: Dict, obj_ids: Set[str], group_ids: Set[str]
) -> Tuple[Dict[str, Dict], Dict[str, Dict]]:
    """
    从全量索引里，按引用 id 提取被引用到的对象/组子集（导出端用）。
    返回 (obj_map, group_map)，结构与 resolve_*_for_export 期望一致：
        {id -> {name, type, category, value}} / {id -> {name, objectIds, expanded_value}}
    索引里查不到的 id 直接跳过（对象可能已删除）。
    """
    objects_by_id = index.get("objects_by_id", {})
    groups_by_id = index.get("groups_by_id", {})
    obj_map = {oid: objects_by_id[oid] for oid in obj_ids if oid in objects_by_id}
    group_map = {gid: groups_by_id[gid] for gid in group_ids if gid in groups_by_id}
    return obj_map, group_map


def resolve_segment_for_export(seg: str, obj_map: Dict[str, Dict],
                               group_map: Dict[str, Dict]) -> str:
    """
    导出端：把单段 cidr 解析成可读文本。
    - OBJ(id)  -> "对象名(实际值)"
    - GRP(id)  -> "组名(成员值1;成员值2)"
    - 字面值（含 VLAN(id).x、IP、Any） -> 原样
    """
    kind, oid = classify_ref_segment(seg)
    if kind == "grp" and oid in group_map:
        g = group_map[oid]
        name = g.get("name", "")
        members = g.get("expanded_value", "")
        return f"{name}({members})" if name else f"Group_{oid}({members})"
    if kind == "obj" and oid in obj_map:
        o = obj_map[oid]
        name = o.get("name", "")
        val = o.get("value", "")
        return f"{name}({val})" if name else f"Obj_{oid}({val})"
    if kind in ("obj", "grp"):
        # 引用了但查不到（对象可能已删除）
        return f"{seg} [未找到]"
    return seg  # 字面值原样（含 VLAN 引用）


def resolve_cidr_for_export(cidr_str: str, obj_map: Dict[str, Dict],
                            group_map: Dict[str, Dict]) -> str:
    """导出端：解析整个 cidr 字段（多段逗号拼接）"""
    segs = split_cidr_segments(cidr_str)
    return ",".join(
        resolve_segment_for_export(s, obj_map, group_map) for s in segs
    )


def parse_resolved_segment(seg: str) -> Tuple[str, str]:
    """
    导入端：从 resolved 列的单段解析出 (匹配键, 实际值)。
    "对象名(实际值)" → ("对象名", "实际值")
    "组名(成员1;成员2)" → ("组名", "成员1;成员2")
    纯字面值 → ("", seg)  实际值就是它本身
    """
    if "(" in seg and seg.endswith(")"):
        name, _, val = seg.partition("(")
        return name.strip(), val[:-1].strip()
    return "", seg


def match_segment_for_import(raw_seg: str, resolved_seg: str,
                             index: Dict,
                             vlan_map: Optional[Dict[str, str]] = None,
                             vlan_passthrough: bool = False
                             ) -> Tuple[Optional[str], str]:
    """
    导入端：把一段值匹配成最终的 cidr 段（OBJ(id)/GRP(id)/子网 或字面值）。
    匹配优先级:
      0. 原始段是 VLAN(tag)[.suffix]
         - vlan_passthrough=True（增量合并用）：原样透传，指向目标站点同号 VLAN
         - 否则（全量导入用）：用 vlan_map 映射成目标网络该 VLAN 的子网；
           命中返回子网 CIDR，未命中返回 (None, ...) 进决策面板
      1. 原始段是 OBJ(id)/GRP(id) 且 resolved 段能解析出值/名 → 在目标 org 索引按值/名匹配
         - 原始是 GRP 优先按组名/组展开值匹配，命中输出 GRP(目标id)
         - 原始是 OBJ 优先按对象名/值匹配，命中输出 OBJ(目标id)
         - 交叉匹配（如原始 GRP 但目标只有同名对象）也接受，输出对应前缀
      2. 原始段是普通字面值（IP/CIDR/FQDN/Any） → 当字面值用
    返回 (最终cidr段, 说明)；匹配失败返回 (None, 说明)，由调用方决定是否进决策面板。
    """
    # 0. VLAN 引用
    vlan_ref = classify_vlan_ref(raw_seg)
    if vlan_ref is not None:
        if vlan_passthrough:
            # 增量合并：原样透传 VLAN(tag)[.suffix]，指向目标站点同号 VLAN
            return raw_seg, f"VLAN 透传"
        tag, _suffix = vlan_ref
        vlan_map = vlan_map or {}
        if tag in vlan_map:
            subnet = vlan_map[tag]
            return subnet, f"VLAN({tag})→子网 {subnet}"
        return None, f"目标网络无 VLAN {tag}"

    kind, _ = classify_ref_segment(raw_seg)
    if kind == "literal":
        return raw_seg, "字面值"

    name, val = parse_resolved_segment(resolved_seg)
    name_to_id = index.get("name_to_id", {})
    value_to_id = index.get("value_to_id", {})
    group_name_to_id = index.get("group_name_to_id", {})
    groups_by_id = index.get("groups_by_id", {})

    # 原始是组：优先按组名 / 组展开值匹配
    if kind == "grp":
        if name and name in group_name_to_id:
            gid = group_name_to_id[name]
            return f"GRP({gid})", f"按组名匹配→{gid}"
        if val:
            for gid, g in groups_by_id.items():
                if g.get("expanded_value") == val:
                    return f"GRP({gid})", f"按组展开值匹配→{gid}"

    # 原始是对象（或组降级到对象匹配）：按对象名 / 实际值匹配
    if name and name in name_to_id:
        return f"OBJ({name_to_id[name]})", f"按对象名匹配→{name_to_id[name]}"
    if val and val in value_to_id:
        return f"OBJ({value_to_id[val]})", f"按值匹配→{value_to_id[val]}"

    # 交叉兜底：原始是组但只匹配到对象名
    if kind == "grp" and name and name in name_to_id:
        return f"OBJ({name_to_id[name]})", f"组降级为对象→{name_to_id[name]}"
    # 原始是对象但只匹配到组
    if kind == "obj":
        if name and name in group_name_to_id:
            gid = group_name_to_id[name]
            return f"GRP({gid})", f"对象升级为组→{gid}"
        if val:
            for gid, g in groups_by_id.items():
                if g.get("expanded_value") == val:
                    return f"GRP({gid})", f"按组展开值匹配→{gid}"
    return None, "目标 org 无匹配"


def resolve_seg_from_source(raw_seg: str, source_index: Dict) -> str:
    """
    当导入规则缺少 resolved 值时（如 CSV 上传场景），用源 org 的对象索引
    按 OBJ(id)/GRP(id) 回查出 "名称(实际值)" 形式的可读文本，供目标匹配用。
    源索引来自 build_object_index(source_org_id)。
    若 raw_seg 不是对象引用或源索引缺失，返回空串。
    """
    kind, oid = classify_ref_segment(raw_seg)
    if kind == "literal" or not source_index:
        return ""
    objects_by_id = source_index.get("objects_by_id", {})
    groups_by_id = source_index.get("groups_by_id", {})
    if kind == "grp" and oid in groups_by_id:
        g = groups_by_id[oid]
        name = g.get("name", "")
        members = g.get("expanded_value", "")
        return f"{name}({members})"
    if kind == "obj" and oid in objects_by_id:
        o = objects_by_id[oid]
        name = o.get("name", "")
        val = o.get("value", "")
        return f"{name}({val})"
    return ""


def is_default_rule(rule: Dict) -> bool:
    """识别默认 deny 规则"""
    return (rule.get("comment", "").strip().lower() == "default rule"
            or rule.get("policy", "").lower() == "deny"
            and rule.get("srcCidr", "").lower() == "any"
            and rule.get("destCidr", "").lower() == "any"
            and rule.get("protocol", "").lower() == "any")


def _source_key_of_rule(rule: Dict) -> str:
    """取规则的「源分块键」用于按 source 分组。
    srcCidr 可能是多段逗号拼接，取第一段作为分块键；
    兜底 Any / 空。用于增量合并的锚点分块展示。"""
    src = (rule.get("srcCidr") or "any").strip()
    if not src:
        return "Any"
    first = split_cidr_segments(src)[0] if split_cidr_segments(src) else "Any"
    return first


def group_rules_by_source(rules: List[Dict],
                          index: Optional[Dict] = None) -> List[Dict]:
    """把规则按 source（srcCidr 第一段）连续分块。
    返回 [{key, label, start, count, has_deny, deny_index, rules:[...]}]：
      - start/count: 该块在原 rules 列表中的起止（连续相同 key 合并）
      - has_deny: 块内是否有 deny any any 兜底规则
      - deny_index: 块内 deny any any 规则的绝对索引（用于锚点=插到 deny 之上）；
        无 deny 时为 None。多 deny 取最后一条（块末尾兜底）。
      - label: 展示名（OBJ/GRP→对象名、VLAN→标签、其余原样）。
    传 index 时用目标 org 索引解析 OBJ/GRP 名（跨 org 正确）；不传则显示原值。
    is_default 规则单独成块。供前端锚点选择器展示。"""
    groups: List[Dict] = []
    for i, r in enumerate(rules):
        key = "默认规则" if is_default_rule(r) else _source_key_of_rule(r)
        # 块级 deny：policy=deny 且 destCidr=any（对任意目的的全量拒绝，即块兜底）。
        # 注意 srcCidr 通常是该块的源（如 VLAN(1102).*），不一定是 any。
        is_block_deny = (
            r.get("policy", "").lower() == "deny"
            and r.get("destCidr", "").lower() == "any"
            and r.get("destPort", "").lower() == "any"
        )
        if groups and groups[-1]["key"] == key:
            groups[-1]["count"] += 1
            groups[-1]["rules"].append(r)
            if is_block_deny:
                groups[-1]["has_deny"] = True
                groups[-1]["deny_index"] = i  # 取最后一条 deny
        else:
            groups.append({
                "key": key,
                "label": _source_label(key, r, index),
                "start": i,
                "count": 1,
                "has_deny": is_block_deny,
                "deny_index": i if is_block_deny else None,
                "rules": [r],
            })
    return groups


def _resolve_cidr_for_display(cidr_str: str, index: Optional[Dict]) -> str:
    """把 cidr 字段里的 OBJ(id)/GRP(id) 段解析成对象名（用于锚点预览可读性）。
    跨 org 时 index 为目标 org 索引；不传则原样返回。VLAN/IP/FQDN 原样。"""
    if not index:
        return cidr_str
    objects_by_id = index.get("objects_by_id", {})
    groups_by_id = index.get("groups_by_id", {})
    return resolve_cidr_for_export(cidr_str, objects_by_id, groups_by_id)


def _source_label(key: str, rule: Dict,
                  index: Optional[Dict] = None) -> str:
    """分块的展示名：OBJ/GRP→对象名(传 index 时解析)、VLAN→VLAN标签、其余原样。"""
    if key == "默认规则":
        return "默认规则(Default rule)"
    # OBJ/GRP 引用：用目标 org 索引解析成名称
    if index:
        m = OBJ_REF_PATTERN.match(key)
        if m:
            kind, oid = m.group(1), m.group(2)
            pool = index.get("groups_by_id" if kind == "GRP" else "objects_by_id", {})
            entry = pool.get(oid)
            if entry:
                return entry.get("name", "") or key
    return key


def _is_valid_cidr_segment(seg: str,
                           allowed_vlans: Optional[Set[str]] = None) -> bool:
    """判断单段 cidr 值是否可被 L3 防火墙 PUT 接受。
    允许: any / IP / CIDR / FQDN / OBJ(id) / GRP(id)。
    VLAN(tag)[.suffix]:
      - tag 在 allowed_vlans 中（目标 MX 上存在的 VLAN）→ 放行
      - 否则拒绝（裸 VLAN 在该 MX 上非法）。
    allowed_vlans 为 None/空时，所有裸 VLAN 都被拒绝（全量导入新站点场景）。"""
    s = seg.strip()
    if not s:
        return False
    low = s.lower()
    if low == "any":
        return True
    # 对象引用
    if OBJ_REF_PATTERN.match(s):
        return True
    # VLAN 引用：仅当 tag 在目标 MX 的 VLAN 集合中才放行
    vlan_ref = classify_vlan_ref(s)
    if vlan_ref is not None:
        tag, _suffix = vlan_ref
        if allowed_vlans and tag in allowed_vlans:
            return True
        return False
    # 多段已在外层拆分，这里 seg 应是单段；若残留逗号则非法
    if "," in s:
        return False
    # FQDN（含字母且非纯 IP/掩码）。支持：
    #   普通域名 api.example.com
    #   通配符域名 *.example.com（Meraki L3 防火墙支持前缀通配符）
    #   含下划线的域名（部分环境使用）
    # 判定标准：含字母、不含斜杠、整体像域名（至少一个点，每段是合法 DNS 字符或通配符）
    if "/" not in s and re.fullmatch(r"(\*|[a-zA-Z0-9_\-]+)(\.(\*|[a-zA-Z0-9_\-]+))+", s):
        return True
    # CIDR / 单 IP（粗校验：数字+点+可选掩码）
    if re.fullmatch(r"\d{1,3}(\.\d{1,3}){3}(/\d{1,2})?", s):
        return True
    # 其它一律判非法（交给 API 之外的本地拦截，给出可读错误）
    return False


def validate_l3_rules(rules: List[Dict],
                      allowed_vlans: Optional[Set[str]] = None) -> List[Dict]:
    """校验规则列表里 srcCidr/destCidr 每段格式。
    allowed_vlans: 目标 MX 上已存在的 VLAN tag 集合；其中的 VLAN 引用放行。
    返回非法段列表 [{index, field, value}]，空列表表示全部合法。"""
    problems: List[Dict] = []
    for i, r in enumerate(rules):
        for field in ("srcCidr", "destCidr"):
            val = r.get(field, "")
            for seg in split_cidr_segments(val):
                if not _is_valid_cidr_segment(seg, allowed_vlans):
                    problems.append({
                        "index": i, "field": field, "value": seg,
                    })
    return problems


def _problem_origin_tag(idx: int, patch_offset: Optional[int],
                         patch_len: int,
                         allowed_vlans: Optional[Set[str]] = None) -> str:
    """为校验报错生成来源标注，帮助定位问题。
    - 区分该规则是「补丁」还是「目标现有规则」（增量合并场景）
    - 不在合并场景（patch_offset 为 None）时返回空串"""
    if patch_offset is None or patch_len <= 0:
        return ""
    if patch_offset <= idx < patch_offset + patch_len:
        return " [补丁规则]"
    return " [目标现有规则]"


# ===========================================================================
# Flask 应用 & 路由
# ===========================================================================
app_client: Optional[MerakiL3FirewallApp] = None
flask_app = Flask(__name__, template_folder="templates")


def get_client() -> MerakiL3FirewallApp:
    global app_client
    if app_client is None:
        app_client = MerakiL3FirewallApp()
    return app_client


@flask_app.errorhandler(RuntimeError)
def handle_runtime_error(e):
    return jsonify({"error": str(e)}), 500


@flask_app.route("/")
def index():
    return render_template("index.html")


@flask_app.route("/api/organizations")
def api_organizations():
    client = get_client()
    orgs = client.get_organizations()
    return jsonify([{"id": o["id"], "name": o.get("name", "")} for o in orgs])


@flask_app.route("/api/networks")
def api_networks():
    org_id = request.args.get("org_id", "")
    if not org_id:
        return jsonify({"error": "缺少 org_id"}), 400
    client = get_client()
    nets = client.get_organization_networks(org_id)
    result = []
    for n in nets:
        # 只展示含 appliance 类型的网络（MX L3 防火墙只在 appliance 上）
        if "appliance" in n.get("productTypes", []):
            result.append({
                "id": n["id"],
                "name": n.get("name", ""),
                "bound_to_template": n.get("isBoundToConfigTemplate", False),
                "config_template_id": n.get("configTemplateId"),
            })
    return jsonify(result)


@flask_app.route("/api/templates")
def api_templates():
    """列出组织下的配置模板（只返回含 appliance 的，可直接读写其 L3 防火墙）"""
    org_id = request.args.get("org_id", "")
    if not org_id:
        return jsonify({"error": "缺少 org_id"}), 400
    client = get_client()
    tmpls = client.get_organization_config_templates(org_id)
    result = []
    for t in tmpls:
        if "appliance" in t.get("productTypes", []):
            result.append({
                "id": t["id"],
                "name": t.get("name", ""),
                "is_template": True,
            })
    return jsonify(result)


@flask_app.route("/api/network-info")
def api_network_info():
    network_id = request.args.get("network_id", "")
    org_id = request.args.get("org_id", "")
    if not network_id:
        return jsonify({"error": "缺少 network_id"}), 400
    client = get_client()
    info = client.resolve_target_id(network_id, org_id)
    return jsonify(info)


@flask_app.route("/api/export")
def api_export():
    """导出 L3 规则（复用导入端的全量对象索引缓存解析引用，生成双列）"""
    org_id = request.args.get("org_id", "")
    network_id = request.args.get("network_id", "")
    if not org_id or not network_id:
        return jsonify({"error": "缺少 org_id 或 network_id"}), 400

    client = get_client()
    print(f"\n{'='*60}\n[导出] org={org_id} network={network_id}")

    # 1. 解析目标 id（处理模板绑定 / 模板本身）
    target = client.resolve_target_id(network_id, org_id)
    print(f"  目标: {target['target_id']} "
          f"(模板={target['bound_to_template']})")

    # 2. 拉 L3 规则
    raw = client.get_l3_rules(target["target_id"])
    rules = raw.get("rules", []) if isinstance(raw, dict) else raw
    print(f"  规则数: {len(rules)}")

    # 3. 建对象索引（带本地缓存：无缓存→全量拉取并写盘；有缓存→抽样校验后直接用）
    #    复用导入端同一份缓存，导出→导入链路只全量拉取一次。
    index = client.build_object_index(org_id)
    print(f"  对象索引: 对象={index['object_count']} 组={index['group_count']}"
          f"{'（命中缓存）' if index.get('cached') else '（新拉取）'}")
    # 从全量索引里按引用 id 提取被引用到的子集
    obj_ids, group_ids = extract_obj_ids(rules)
    obj_map, group_map = select_referenced_from_index(index, obj_ids, group_ids)
    print(f"  引用解析: 对象={len(obj_map)}/{len(obj_ids)} "
          f"组={len(group_map)}/{len(group_ids)}")

    # 4. 生成双列
    out_rules = []
    for r in rules:
        src_raw = r.get("srcCidr", "Any")
        dst_raw = r.get("destCidr", "Any")
        out_rules.append({
            "comment": r.get("comment", ""),
            "policy": r.get("policy", "allow"),
            "protocol": r.get("protocol", "any"),
            "srcPort": r.get("srcPort", "Any"),
            "srcCidr": src_raw,
            "srcCidr_resolved": resolve_cidr_for_export(src_raw, obj_map, group_map),
            "destPort": r.get("destPort", "Any"),
            "destCidr": dst_raw,
            "destCidr_resolved": resolve_cidr_for_export(dst_raw, obj_map, group_map),
            "syslogEnabled": bool(r.get("syslogEnabled", False)),
            "is_default": is_default_rule(r),
        })

    # 对象清单（供参考）
    objects_map = []
    for oid, o in obj_map.items():
        objects_map.append({
            "obj_id": oid, "name": o.get("name", ""),
            "type": o.get("type", ""), "category": o.get("category", ""),
            "value": o.get("value", ""),
        })
    for gid, g in group_map.items():
        objects_map.append({
            "obj_id": gid, "name": g.get("name", ""),
            "type": "group", "category": "NetworkObjectGroup",
            "value": g.get("expanded_value", ""),
        })

    return jsonify({
        "rules": out_rules,
        "objects_map": objects_map,
        "context": target,
    })


# CSV 列（批量备份）：原始 OBJ(id)/GRP(id) 与名称化双列
BACKUP_CSV_HEADER = [
    "comment", "policy", "protocol",
    "srcPort", "srcCidr", "srcCidr_resolved",
    "destPort", "destCidr", "destCidr_resolved",
    "syslogEnabled",
]

_ILLEGAL_FNAME = re.compile(r'[\\/:*?"<>|]+')


def _safe_filename(name: str) -> str:
    """去除文件名非法字符，用于 ZIP 内条目命名。"""
    cleaned = _ILLEGAL_FNAME.sub("_", (name or "").strip())
    return cleaned or "site"


def _build_backup_csv(client: "MerakiL3FirewallApp", target: Dict,
                      index: Dict) -> str:
    """拉取单站点 L3 规则，生成含双列（原始 + 名称化）的 CSV 文本（含 UTF-8 BOM）。"""
    raw = client.get_l3_rules(target["target_id"])
    rules = raw.get("rules", []) if isinstance(raw, dict) else raw
    obj_ids, group_ids = extract_obj_ids(rules)
    obj_map, group_map = select_referenced_from_index(index, obj_ids, group_ids)
    buf = io.StringIO()
    writer = csv.writer(buf)
    writer.writerow(BACKUP_CSV_HEADER)
    for r in rules:
        src_raw = r.get("srcCidr", "Any")
        dst_raw = r.get("destCidr", "Any")
        writer.writerow([
            r.get("comment", ""),
            r.get("policy", "allow"),
            r.get("protocol", "any"),
            r.get("srcPort", "Any"),
            src_raw,
            resolve_cidr_for_export(src_raw, obj_map, group_map),
            r.get("destPort", "Any"),
            dst_raw,
            resolve_cidr_for_export(dst_raw, obj_map, group_map),
            bool(r.get("syslogEnabled", False)),
        ])
    return "\ufeff" + buf.getvalue()


@flask_app.route("/api/backup/batch", methods=["POST"])
def api_backup_batch():
    """批量备份：对多个站点/模板逐个导出 L3 规则 CSV，打包为 ZIP 返回。
    body: {targets: [{network_id, org_id}]}。单站点失败写入 _errors.txt，不中断其他。"""
    data = request.get_json(force=True)
    targets = data.get("targets", [])
    if not targets:
        return jsonify({"error": "缺少 targets"}), 400

    client = get_client()
    print(f"\n{'='*60}\n[批量备份] 站点 {len(targets)} 个")

    buf = io.BytesIO()
    errors: List[str] = []
    ok_count = 0
    used_names: Set[str] = set()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as zf:
        for t in targets:
            net_id = t.get("network_id", "")
            org_id = t.get("org_id", "")
            try:
                if not net_id or not org_id:
                    raise ValueError("target 缺少 network_id 或 org_id")
                target = client.resolve_target_id(net_id, org_id)
                index = client.build_object_index(org_id)
                csv_text = _build_backup_csv(client, target, index)
                base = _safe_filename(target.get("network_name", "") or net_id)
                fname = f"{base}_{net_id}.csv"
                # 防重名
                suffix = 1
                while fname in used_names:
                    fname = f"{base}_{net_id}_{suffix}.csv"
                    suffix += 1
                used_names.add(fname)
                zf.writestr(fname, csv_text)
                ok_count += 1
                print(f"  [ok] {net_id} → {fname}")
            except Exception as e:
                print(f"  [error] {net_id}: {e}")
                errors.append(f"{net_id} ({org_id}): {e}")
        if errors:
            zf.writestr("_errors.txt", "\n".join(errors))

    if ok_count == 0:
        return jsonify({"error": "所有站点备份失败", "details": errors}), 500

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    fname = f"firewall_backup_{ts}.zip"
    return Response(
        buf.getvalue(),
        mimetype="application/zip",
        headers={"Content-Disposition": f"attachment; filename={fname}"},
    )


@flask_app.route("/api/objects-index")
def api_objects_index():
    """导入前：全量拉取目标 org 对象建索引（带缓存）"""
    org_id = request.args.get("org_id", "")
    force = request.args.get("force", "false").lower() == "true"
    if not org_id:
        return jsonify({"error": "缺少 org_id"}), 400
    client = get_client()
    index = client.build_object_index(org_id, force_refresh=force)
    # 只返回统计 + 给前端展示用（不返回完整索引避免响应过大）
    return jsonify({
        "object_count": index["object_count"],
        "group_count": index["group_count"],
        "built_at": index.get("built_at", ""),
        "cached": index.get("cached", False),
    })


@flask_app.route("/api/objects-data")
def api_objects_data():
    """返回精简的完整对象索引（供前端搜索 + name↔id 转换）。
    复用 build_object_index 的本地缓存。"""
    org_id = request.args.get("org_id", "")
    if not org_id:
        return jsonify({"error": "缺少 org_id"}), 400
    client = get_client()
    index = client.build_object_index(org_id)
    # 精简：只取前端需要的字段，不传 name_to_id/value_to_id 等反查表
    objects = [
        {
            "id": oid,
            "name": o.get("name", ""),
            "type": o.get("type", ""),
            "value": o.get("value", ""),
        }
        for oid, o in index.get("objects_by_id", {}).items()
    ]
    groups = [
        {
            "id": gid,
            "name": g.get("name", ""),
            "value": g.get("expanded_value", ""),
            "objectIds": g.get("objectIds", []),
        }
        for gid, g in index.get("groups_by_id", {}).items()
    ]
    return jsonify({
        "objects": objects,
        "groups": groups,
        "built_at": index.get("built_at", ""),
        "cached": index.get("cached", False),
    })


def _create_objects_from_decisions(client: "MerakiL3FirewallApp", org_id: str,
                                  decisions: Dict) -> Tuple[Dict[str, str], int]:
    """根据决策中 action=create 的条目在目标 org 创建 Policy Object。
    返回 (value_to_new_objid, created_count)。创建失败的条目回退当字面值处理。"""
    value_to_new_objid: Dict[str, str] = {}
    created_count = 0
    for value, dec in decisions.items():
        if dec.get("action", "literal") != "create":
            continue
        new_name = dec.get("new_name") or value
        payload = client._guess_object_payload(value, new_name)
        try:
            created = client.create_policy_object(org_id, payload)
            nid = str(created.get("id"))
            value_to_new_objid[value] = nid
            created_count += 1
            print(f"  创建对象: {new_name}={value} → {nid}")
        except RuntimeError as e:
            print(f"  [warn] 创建对象失败 {new_name}: {e}")
            # 失败则回退当字面值
    return value_to_new_objid, created_count


def _preview_import_for_target(client: "MerakiL3FirewallApp", rules: List[Dict],
                              target: Dict, index: Dict,
                              source_index: Optional[Dict]
                              ) -> Tuple[List[Dict], List[Dict], Dict, str]:
    """针对单个目标站点做全量导入预检匹配，返回 (preview, missing, backup_data, backup_file)。
    仅备份现有规则，不写入。missing 中 rule_index 指向 rules 列表中的原始下标。"""
    vlan_map = client.build_vlan_map(target["target_id"])
    missing: List[Dict] = []
    preview: List[Dict] = []
    for i, r in enumerate(rules):
        if r.get("is_default"):
            continue
        final_rule = {
            "comment": r.get("comment", ""),
            "policy": r.get("policy", "allow"),
            "protocol": r.get("protocol", "any"),
            "srcPort": r.get("srcPort", "Any"),
            "srcCidr": "",
            "destPort": r.get("destPort", "Any"),
            "destCidr": "",
            "syslogEnabled": bool(r.get("syslogEnabled", False)),
        }
        for field, raw_key, res_key in (
            ("srcCidr", "srcCidr", "srcCidr_resolved"),
            ("destCidr", "destCidr", "destCidr_resolved"),
        ):
            raw_segs = split_cidr_segments(r.get(raw_key, ""))
            res_segs = split_cidr_segments(r.get(res_key, ""))
            while len(res_segs) < len(raw_segs):
                res_segs.append("")
            final_segs = []
            for j, raw_seg in enumerate(raw_segs):
                res_seg = res_segs[j] if j < len(res_segs) else ""
                if not res_seg:
                    res_seg = resolve_seg_from_source(raw_seg, source_index or {})
                final, note = match_segment_for_import(
                    raw_seg, res_seg, index, vlan_map
                )
                if final is None:
                    _, val = parse_resolved_segment(res_seg)
                    vlan_ref = classify_vlan_ref(raw_seg)
                    disp_value = raw_seg if vlan_ref is not None else (val or raw_seg)
                    missing.append({
                        "rule_index": i,
                        "field": field,
                        "value": disp_value,
                        "raw_seg": raw_seg,
                        "res_seg": res_seg,
                        "is_vlan": vlan_ref is not None,
                    })
                    final_segs.append("__PENDING__")
                else:
                    final_segs.append(final)
            final_rule[field] = ",".join(final_segs)
        preview.append(final_rule)
    # 备份现有规则
    backup = client.get_l3_rules(target["target_id"])
    backup_file = client.write_backup(target["network_id"], backup)
    return preview, missing, backup, backup_file


def _confirm_import_for_target(client: "MerakiL3FirewallApp", rules: List[Dict],
                               target: Dict, index: Dict,
                               source_index: Optional[Dict],
                               value_to_new_objid: Dict[str, str],
                               decisions: Dict
                               ) -> Tuple[List[Dict], int, bool]:
    """针对单个目标应用决策构建最终规则，返回 (final_rules, skipped, syslog_default)。不执行 PUT。
    对象创建（decisions 中 action=create）需由调用方预先完成并传入 value_to_new_objid。"""
    vlan_map = client.build_vlan_map(target["target_id"])
    final_rules: List[Dict] = []
    skipped = 0
    for i, r in enumerate(rules):
        if r.get("is_default"):
            continue
        final_rule = {
            "comment": r.get("comment", ""),
            "policy": r.get("policy", "allow"),
            "protocol": r.get("protocol", "any"),
            "srcPort": r.get("srcPort", "Any"),
            "srcCidr": "",
            "destPort": r.get("destPort", "Any"),
            "destCidr": "",
            "syslogEnabled": bool(r.get("syslogEnabled", False)),
        }
        skip_this = False
        for field, raw_key, res_key in (
            ("srcCidr", "srcCidr", "srcCidr_resolved"),
            ("destCidr", "destCidr", "destCidr_resolved"),
        ):
            raw_segs = split_cidr_segments(r.get(raw_key, ""))
            res_segs = split_cidr_segments(r.get(res_key, ""))
            while len(res_segs) < len(raw_segs):
                res_segs.append("")
            out_segs = []
            for j, raw_seg in enumerate(raw_segs):
                res_seg = res_segs[j] if j < len(res_segs) else ""
                if not res_seg:
                    res_seg = resolve_seg_from_source(raw_seg, source_index or {})
                out = client._apply_import_segment(
                    raw_seg, res_seg, index, value_to_new_objid, decisions, vlan_map
                )
                if out is None:
                    skip_this = True
                    break
                out_segs.append(out)
            if skip_this:
                break
            final_rule[field] = ",".join(out_segs)
        if skip_this:
            skipped += 1
            continue
        final_rules.append(final_rule)
    # 默认规则的 syslogEnabled → 顶层 syslogDefaultRule
    syslog_default = False
    for r in rules:
        if r.get("is_default"):
            syslog_default = bool(r.get("syslogEnabled", False))
    return final_rules, skipped, syslog_default


def _resolve_source_index(client: "MerakiL3FirewallApp", source_org_id: str,
                          org_id: str, index: Dict) -> Optional[Dict]:
    """构建源 org 对象索引（供 CSV/无 resolved 场景回查）；同 org 直接复用目标索引。"""
    if source_org_id and source_org_id != org_id:
        try:
            return client.build_object_index(source_org_id)
        except Exception as e:
            print(f"  [warn] 源索引构建失败: {e}")
            return None
    if source_org_id == org_id:
        return index
    return None


@flask_app.route("/api/import", methods=["POST"])
def api_import_preview():
    """导入预检（单站点）：匹配对象，返回缺失项 + 预览 + 备份，不写入"""
    data = request.get_json(force=True)
    org_id = data.get("org_id", "")
    network_id = data.get("network_id", "")
    source_org_id = data.get("source_org_id", "")
    rules = data.get("rules", [])
    if not org_id or not network_id:
        return jsonify({"error": "缺少 org_id 或 network_id"}), 400

    client = get_client()
    print(f"\n{'='*60}\n[导入预检] org={org_id} network={network_id} 规则={len(rules)}")

    target = client.resolve_target_id(network_id, org_id)
    print(f"  目标: {target['target_id']} (模板={target['bound_to_template']})")
    index = client.build_object_index(org_id)
    print(f"  目标索引: 对象={index['object_count']} 组={index['group_count']}")
    source_index = _resolve_source_index(client, source_org_id, org_id, index)

    preview, missing, backup, backup_file = _preview_import_for_target(
        client, rules, target, index, source_index
    )
    print(f"  缺失对象: {len(missing)} 备份: {backup_file}")
    return jsonify({
        "missing": missing,
        "preview": preview,
        "context": target,
        "object_count": index["object_count"],
        "group_count": index["group_count"],
        "backup_file": os.path.basename(backup_file) if backup_file else "",
        "backup_data": backup,
    })


@flask_app.route("/api/import/confirm", methods=["POST"])
def api_import_confirm():
    """确认导入：应用决策（创建对象/当字面值/跳过），执行 PUT"""
    data = request.get_json(force=True)
    org_id = data.get("org_id", "")
    network_id = data.get("network_id", "")
    source_org_id = data.get("source_org_id", "")
    rules = data.get("rules", [])
    decisions = data.get("decisions", {})  # {value: {action, new_name}}
    if not org_id or not network_id:
        return jsonify({"error": "缺少 org_id 或 network_id"}), 400

    client = get_client()
    print(f"\n{'='*60}\n[导入确认] org={org_id} network={network_id}")

    target = client.resolve_target_id(network_id, org_id)
    index = client.build_object_index(org_id)
    print(f"  目标: {target['target_id']} (模板={target['bound_to_template']})")

    # 源索引（用于 CSV/无 resolved 场景回查对象实际值）
    source_index = _resolve_source_index(client, source_org_id, org_id, index)

    # 处理决策：创建对象，建立 value -> OBJ_ID 映射
    value_to_new_objid, created_count = _create_objects_from_decisions(
        client, org_id, decisions
    )

    # 构建最终规则（应用决策 + 匹配）
    final_rules, skipped, syslog_default = _confirm_import_for_target(
        client, rules, target, index, source_index, value_to_new_objid, decisions
    )

    print(f"  最终规则: {len(final_rules)} 跳过: {skipped} 新建对象: {created_count}")

    # 执行 PUT
    result = client.update_l3_rules(
        target["target_id"], final_rules, syslog_default
    )
    resp_rules = result.get("rules", result) if isinstance(result, dict) else result
    return jsonify({
        "success": True,
        "context": target,
        "rules_written": len(final_rules),
        "rules_skipped": skipped,
        "objects_created": created_count,
        "response_rules_count": len(resp_rules) if isinstance(resp_rules, list) else None,
    })


# ===========================================================================
# 增量合并导入：把补丁规则拼接进目标站点现有规则（局部变更）
# ===========================================================================
def _build_patch_for_target(client: MerakiL3FirewallApp, patch_rules: List[Dict],
                            target_id: str, org_id: str, source_org_id: str,
                            index: Dict, source_index: Optional[Dict],
                            vlan_passthrough: bool, apply_decisions: bool,
                            decisions: Dict, value_to_new_objid: Dict[str, str]
                            ) -> Tuple[List[Dict], List[Dict]]:
    """把补丁规则针对单个目标站点重映射（OBJ/GRP→目标id；VLAN 按模式透传或映射子网）。
    返回 (final_patch_rules, missing)。missing 仅在 apply_decisions=False（预检）时收集。
    目标站点的现有规则不在此处理（绝不重映射）。
    """
    vlan_map = {} if vlan_passthrough else client.build_vlan_map(target_id)
    final_patch: List[Dict] = []
    missing: List[Dict] = []
    for i, r in enumerate(patch_rules):
        if r.get("is_default"):
            continue
        final_rule = {
            "comment": r.get("comment", ""),
            "policy": r.get("policy", "allow"),
            "protocol": r.get("protocol", "any"),
            "srcPort": r.get("srcPort", "Any"),
            "srcCidr": "",
            "destPort": r.get("destPort", "Any"),
            "destCidr": "",
            "syslogEnabled": bool(r.get("syslogEnabled", False)),
        }
        skip_this = False
        for field, raw_key, res_key in (
            ("srcCidr", "srcCidr", "srcCidr_resolved"),
            ("destCidr", "destCidr", "destCidr_resolved"),
        ):
            raw_segs = split_cidr_segments(r.get(raw_key, ""))
            res_segs = split_cidr_segments(r.get(res_key, ""))
            while len(res_segs) < len(raw_segs):
                res_segs.append("")
            out_segs = []
            for j, raw_seg in enumerate(raw_segs):
                res_seg = res_segs[j] if j < len(res_segs) else ""
                if not res_seg:
                    res_seg = resolve_seg_from_source(raw_seg, source_index or {})
                if apply_decisions:
                    out = client._apply_import_segment(
                        raw_seg, res_seg, index, value_to_new_objid, decisions,
                        vlan_map, vlan_passthrough
                    )
                    if out is None:
                        skip_this = True
                        break
                    out_segs.append(out)
                else:
                    final, note = match_segment_for_import(
                        raw_seg, res_seg, index, vlan_map, vlan_passthrough
                    )
                    if final is None:
                        _, val = parse_resolved_segment(res_seg)
                        vlan_ref = classify_vlan_ref(raw_seg)
                        disp_value = raw_seg if vlan_ref is not None else (val or raw_seg)
                        missing.append({
                            "rule_index": i, "field": field,
                            "value": disp_value, "raw_seg": raw_seg, "res_seg": res_seg,
                            "is_vlan": vlan_ref is not None,
                        })
                        out_segs.append("__PENDING__")
                    else:
                        out_segs.append(final)
            if skip_this:
                break
            final_rule[field] = ",".join(out_segs)
        if skip_this:
            continue
        final_patch.append(final_rule)
    return final_patch, missing


@flask_app.route("/api/import/merge", methods=["POST"])
def api_import_merge_preview():
    """增量合并预检（只读）：针对单个目标站点，返回补丁重映射结果 + 目标规则分块 + 缺失对象。
    前端批量场景逐站点调本接口，合并 missing 后统一决策。"""
    data = request.get_json(force=True)
    org_id = data.get("org_id", "")
    network_id = data.get("network_id", "")
    source_org_id = data.get("source_org_id", "")
    patch_rules = data.get("rules", [])
    if not org_id or not network_id:
        return jsonify({"error": "缺少 org_id 或 network_id"}), 400

    client = get_client()
    print(f"\n{'='*60}\n[增量合并预检] org={org_id} network={network_id} 补丁={len(patch_rules)}")

    target = client.resolve_target_id(network_id, org_id)
    index = client.build_object_index(org_id)

    # 源索引（补丁规则可能缺 _resolved，按源 org 回查）
    source_index = None
    if source_org_id and source_org_id != org_id:
        try:
            source_index = client.build_object_index(source_org_id)
        except Exception as e:
            print(f"  [warn] 源索引构建失败: {e}")
    elif source_org_id == org_id:
        source_index = index

    # 读目标当前规则（原样保留，绝不重映射）
    raw_target = client.get_l3_rules(target["target_id"])
    target_rules = raw_target.get("rules", []) if isinstance(raw_target, dict) else raw_target
    print(f"  目标现有规则: {len(target_rules)} 条")

    # 补丁重映射（VLAN 透传，OBJ/GRP 按目标 org 重映射）
    patch_preview, missing = _build_patch_for_target(
        client, patch_rules, target["target_id"], org_id, source_org_id,
        index, source_index, vlan_passthrough=True,
        apply_decisions=False, decisions={}, value_to_new_objid={},
    )
    print(f"  补丁重映射: {len(patch_preview)} 条, 缺失对象: {len(missing)}")

    # 目标规则按 source 分块（用目标 org 索引解析 OBJ/GRP 名，供前端锚点选择可读展示）
    target_grouped = group_rules_by_source(target_rules, index)
    # 给每条规则补上 srcCidr_resolved/destCidr_resolved（名称化），前端预览直接用
    for g in target_grouped:
        g["rules"] = [{
            **r,
            "srcCidr_resolved": _resolve_cidr_for_display(r.get("srcCidr", ""), index),
            "destCidr_resolved": _resolve_cidr_for_display(r.get("destCidr", ""), index),
        } for r in g["rules"]]

    return jsonify({
        "patch_preview": patch_preview,
        "target_grouped": target_grouped,
        "target_rules_count": len(target_rules),
        "missing": missing,
        "context": target,
        "object_count": index["object_count"],
        "group_count": index["group_count"],
    })


@flask_app.route("/api/import/merge/confirm", methods=["POST"])
def api_import_merge_confirm():
    """增量合并确认（写入）：对每个目标站点读现有规则→拼接补丁→PUT 全量。
    targets: [{network_id, org_id, anchor}]，anchor 为目标规则列表中的插入位置索引。
    逐站点独立备份 + 独立错误处理，单站点失败不影响其他。"""
    data = request.get_json(force=True)
    source_org_id = data.get("source_org_id", "")
    patch_rules = data.get("rules", [])
    decisions = data.get("decisions", {})
    targets = data.get("targets", [])
    if not targets:
        return jsonify({"error": "缺少 targets"}), 400

    client = get_client()
    print(f"\n{'='*60}\n[增量合并确认] 目标站点 {len(targets)} 个, 补丁 {len(patch_rules)} 条")

    # 源索引（统一构建一次）
    source_index = None
    if source_org_id:
        try:
            source_index = client.build_object_index(source_org_id)
        except Exception as e:
            print(f"  [warn] 源索引构建失败: {e}")

    results = []
    rollback_sites: List[Dict] = []
    for t in targets:
        net_id = t.get("network_id", "")
        org_id = t.get("org_id", "")
        anchor = t.get("anchor", 0)
        try:
            if not net_id or not org_id:
                raise ValueError("target 缺少 network_id 或 org_id")

            target = client.resolve_target_id(net_id, org_id)
            index = client.build_object_index(org_id)

            # 决策：创建对象（本 org 独立创建；按值匹配优先避免重复）
            value_to_new_objid: Dict[str, str] = {}
            created_in_this_target = 0
            for value, dec in decisions.items():
                if dec.get("action") != "create":
                    continue
                # 已有同名同值对象则复用
                if value in index.get("value_to_id", {}):
                    value_to_new_objid[value] = index["value_to_id"][value]
                    continue
                new_name = dec.get("new_name") or value
                payload = client._guess_object_payload(value, new_name)
                try:
                    created = client.create_policy_object(org_id, payload)
                    nid = str(created.get("id"))
                    value_to_new_objid[value] = nid
                    created_in_this_target += 1
                except RuntimeError as e:
                    print(f"  [warn] {net_id} 创建对象失败 {new_name}: {e}")

            # 补丁重映射（应用决策）
            final_patch, _ = _build_patch_for_target(
                client, patch_rules, target["target_id"], org_id, source_org_id,
                index, source_index, vlan_passthrough=True,
                apply_decisions=True, decisions=decisions,
                value_to_new_objid=value_to_new_objid,
            )
            if not final_patch:
                raise ValueError("补丁重映射后为空（规则可能被决策跳过）")

            # 读目标现有规则
            raw_target = client.get_l3_rules(target["target_id"])
            target_rules = raw_target.get("rules", []) if isinstance(raw_target, dict) else raw_target

            # 备份（供一键倒回）
            backup_file = client.write_backup(net_id, raw_target)

            # 拼接：anchor 为插入位置（目标规则索引），clamp 到有效范围
            anchor = max(0, min(int(anchor), len(target_rules)))
            merged_rules = target_rules[:anchor] + final_patch + target_rules[anchor:]

            # 保留目标 syslogDefaultRule（从目标规则提取，不用补丁的）
            syslog_default = False
            for tr in target_rules:
                if is_default_rule(tr):
                    syslog_default = bool(tr.get("syslogEnabled", False))
                    break

            print(f"  {net_id}: 拼接 {len(final_patch)} 条到位置 {anchor}, "
                  f"合并后 {len(merged_rules)} 条, 新建对象 {created_in_this_target}")

            # 目标 MX 上已存在的 VLAN tag 集合：合并后规则里的 VLAN 引用
            # （包括目标规则自身的 + 补丁透传的同号 VLAN）只要 tag 存在就合法。
            # 用 get_appliance_vlan_tags（含 subnet 为空的模板 VLAN），不能用 build_vlan_map
            # （后者只含有子网的 VLAN，会漏掉 unique 型模板 VLAN 导致误判）。
            target_vlan_tags = client.get_appliance_vlan_tags(target["target_id"])

            result = client.update_l3_rules(
                target["target_id"], merged_rules, syslog_default,
                allowed_vlans=target_vlan_tags,
                patch_offset=anchor, patch_len=len(final_patch),
            )
            resp_rules = result.get("rules", result) if isinstance(result, dict) else result
            if backup_file:
                rollback_sites.append({
                    "network_id": net_id,
                    "target_id": target["target_id"],
                    "network_name": target.get("network_name", ""),
                    "org_id": org_id,
                    "backup_file": os.path.basename(backup_file),
                    "syslog_default": syslog_default,
                })
            results.append({
                "network_id": net_id,
                "network_name": target.get("network_name", ""),
                "success": True,
                "rules_inserted": len(final_patch),
                "rules_total": len(resp_rules) if isinstance(resp_rules, list) else None,
                "objects_created": created_in_this_target,
                "anchor": anchor,
            })
        except Exception as e:
            print(f"  [error] {net_id}: {e}")
            results.append({
                "network_id": net_id,
                "success": False,
                "error": str(e),
            })

    succeeded = sum(1 for r in results if r["success"])
    batch_id = _record_rollback_batch("merge", rollback_sites)
    print(f"  汇总: {succeeded}/{len(results)} 成功  batch_id={batch_id}")
    return jsonify({
        "results": results,
        "succeeded": succeeded,
        "total": len(results),
        "batch_id": batch_id,
    })


# ===========================================================================
# 一键倒回：从 rollback_index 找到批次 → 读备份文件 → 还原目标站点规则
# ===========================================================================
@flask_app.route("/api/rollback/list", methods=["GET"])
def api_rollback_list():
    """返回最近的可倒回批次列表（最新在前）。"""
    idx = _load_rollback_index()
    batches = []
    for b in reversed(idx.get("batches", [])):
        sites = b.get("sites", [])
        batches.append({
            "batch_id": b.get("batch_id", ""),
            "op_type": b.get("op_type", ""),
            "created_at": b.get("created_at", ""),
            "site_count": len(sites),
            "sites": [
                {"network_id": s.get("network_id", ""),
                 "network_name": s.get("network_name", "")}
                for s in sites
            ],
        })
    return jsonify({"batches": batches})


def _rollback_one_site(client: "MerakiL3FirewallApp", site: Dict) -> Dict:
    """将单个站点还原到其备份文件记录的规则（含 syslogDefaultRule）。"""
    net_id = site.get("network_id", "")
    backup_file = site.get("backup_file", "")
    try:
        target_id = site.get("target_id", "") or net_id
        path = os.path.join(CACHE_DIR, os.path.basename(backup_file))
        if not backup_file or not os.path.exists(path):
            raise ValueError(f"备份文件不存在: {backup_file}")
        with open(path, "r", encoding="utf-8") as f:
            raw = json.load(f)
        rules = raw.get("rules", []) if isinstance(raw, dict) else raw
        # 去除默认规则（API PUT 不接受显式默认规则），提取 syslogDefaultRule
        syslog_default = bool(raw.get("syslogDefaultRule", False)) if isinstance(raw, dict) else False
        restore_rules = []
        for r in rules:
            if is_default_rule(r):
                syslog_default = bool(r.get("syslogEnabled", syslog_default))
                continue
            restore_rules.append(r)
        # 含 VLAN 引用的站点还原时用已存在 tag 集合放行校验
        allowed = client.get_appliance_vlan_tags(target_id)
        client.update_l3_rules(target_id, restore_rules, syslog_default,
                               allowed_vlans=allowed)
        return {
            "network_id": net_id,
            "network_name": site.get("network_name", ""),
            "success": True,
            "rules_restored": len(restore_rules),
        }
    except Exception as e:
        print(f"  [error] 倒回 {net_id}: {e}")
        return {
            "network_id": net_id,
            "network_name": site.get("network_name", ""),
            "success": False,
            "error": str(e),
        }


@flask_app.route("/api/rollback", methods=["POST"])
def api_rollback():
    """一键倒回：body {batch_id, network_id?(可选，仅倒回单站点)}。
    逐站点独立错误处理，返回 {results, succeeded, total}。"""
    data = request.get_json(force=True)
    batch_id = data.get("batch_id", "")
    only_net = data.get("network_id", "")
    if not batch_id:
        return jsonify({"error": "缺少 batch_id"}), 400

    idx = _load_rollback_index()
    batch = next((b for b in idx.get("batches", []) if b.get("batch_id") == batch_id), None)
    if not batch:
        return jsonify({"error": f"未找到批次 {batch_id}"}), 404

    sites = batch.get("sites", [])
    if only_net:
        sites = [s for s in sites if s.get("network_id") == only_net]
        if not sites:
            return jsonify({"error": f"批次中无站点 {only_net}"}), 404

    client = get_client()
    print(f"\n{'='*60}\n[一键倒回] batch={batch_id} 站点 {len(sites)} 个")
    results = [_rollback_one_site(client, s) for s in sites]
    succeeded = sum(1 for r in results if r["success"])
    print(f"  汇总: {succeeded}/{len(results)} 成功")
    return jsonify({"results": results, "succeeded": succeeded, "total": len(results)})


# ===========================================================================
# 批量全量导入：多目标站点统一预检（缺失对象去重合并）+ 统一决策写入
# ===========================================================================
@flask_app.route("/api/import/batch", methods=["POST"])
def api_import_batch_preview():
    """批量全量导入预检：body {targets:[{network_id,org_id}], rules, source_org_id}。
    逐站点 preview，各站点 missing 按 value 去重合并为统一 missing。"""
    data = request.get_json(force=True)
    targets = data.get("targets", [])
    rules = data.get("rules", [])
    source_org_id = data.get("source_org_id", "")
    if not targets:
        return jsonify({"error": "缺少 targets"}), 400

    client = get_client()
    print(f"\n{'='*60}\n[批量导入预检] 目标 {len(targets)} 个, 规则 {len(rules)} 条")

    per_site = []
    merged_missing: Dict[str, Dict] = {}
    for t in targets:
        net_id = t.get("network_id", "")
        org_id = t.get("org_id", "")
        try:
            if not net_id or not org_id:
                raise ValueError("target 缺少 network_id 或 org_id")
            target = client.resolve_target_id(net_id, org_id)
            index = client.build_object_index(org_id)
            source_index = _resolve_source_index(client, source_org_id, org_id, index)
            preview, missing, _backup, backup_file = _preview_import_for_target(
                client, rules, target, index, source_index
            )
            for m in missing:
                key = m["value"]
                if key not in merged_missing:
                    merged_missing[key] = {
                        "value": m["value"],
                        "raw_seg": m["raw_seg"],
                        "res_seg": m["res_seg"],
                        "is_vlan": m["is_vlan"],
                    }
            per_site.append({
                "network_id": net_id,
                "network_name": target.get("network_name", ""),
                "preview_count": len(preview),
                "missing_count": len(missing),
                "backup_file": os.path.basename(backup_file) if backup_file else "",
            })
            print(f"  [ok] {net_id}: 预览 {len(preview)} 缺失 {len(missing)}")
        except Exception as e:
            print(f"  [error] {net_id}: {e}")
            per_site.append({
                "network_id": net_id,
                "network_name": t.get("network_name", ""),
                "error": str(e),
            })

    return jsonify({
        "per_site": per_site,
        "missing": list(merged_missing.values()),
    })


@flask_app.route("/api/import/batch/confirm", methods=["POST"])
def api_import_batch_confirm():
    """批量全量导入写入：body {targets, rules, decisions, source_org_id}。
    逐站点：创建对象（按值去重复用）→ 构建规则 → 备份 → 全量 PUT；
    逐站点独立错误处理；循环后记录回滚批次。"""
    data = request.get_json(force=True)
    targets = data.get("targets", [])
    rules = data.get("rules", [])
    decisions = data.get("decisions", {})
    source_org_id = data.get("source_org_id", "")
    if not targets:
        return jsonify({"error": "缺少 targets"}), 400

    client = get_client()
    print(f"\n{'='*60}\n[批量导入确认] 目标 {len(targets)} 个")

    results = []
    rollback_sites: List[Dict] = []
    for t in targets:
        net_id = t.get("network_id", "")
        org_id = t.get("org_id", "")
        try:
            if not net_id or not org_id:
                raise ValueError("target 缺少 network_id 或 org_id")
            target = client.resolve_target_id(net_id, org_id)
            index = client.build_object_index(org_id)
            source_index = _resolve_source_index(client, source_org_id, org_id, index)

            # 决策：创建对象（本 org 独立；已有同值对象则复用）
            value_to_new_objid: Dict[str, str] = {}
            created_in_this_target = 0
            for value, dec in decisions.items():
                if dec.get("action") != "create":
                    continue
                if value in index.get("value_to_id", {}):
                    value_to_new_objid[value] = index["value_to_id"][value]
                    continue
                new_name = dec.get("new_name") or value
                payload = client._guess_object_payload(value, new_name)
                try:
                    created = client.create_policy_object(org_id, payload)
                    value_to_new_objid[value] = str(created.get("id"))
                    created_in_this_target += 1
                except RuntimeError as e:
                    print(f"  [warn] {net_id} 创建对象失败 {new_name}: {e}")

            # 备份现有规则（供一键倒回）
            raw_target = client.get_l3_rules(target["target_id"])
            backup_file = client.write_backup(net_id, raw_target)

            # 构建最终规则（应用决策）
            final_rules, skipped, syslog_default = _confirm_import_for_target(
                client, rules, target, index, source_index,
                value_to_new_objid, decisions
            )

            # 含 VLAN 引用的站点全量导入时用已存在 tag 集合放行校验
            allowed = client.get_appliance_vlan_tags(target["target_id"])
            result = client.update_l3_rules(
                target["target_id"], final_rules, syslog_default,
                allowed_vlans=allowed,
            )
            resp_rules = result.get("rules", result) if isinstance(result, dict) else result
            if backup_file:
                rollback_sites.append({
                    "network_id": net_id,
                    "target_id": target["target_id"],
                    "network_name": target.get("network_name", ""),
                    "org_id": org_id,
                    "backup_file": os.path.basename(backup_file),
                    "syslog_default": syslog_default,
                })
            results.append({
                "network_id": net_id,
                "network_name": target.get("network_name", ""),
                "success": True,
                "rules_written": len(final_rules),
                "rules_skipped": skipped,
                "objects_created": created_in_this_target,
                "rules_total": len(resp_rules) if isinstance(resp_rules, list) else None,
            })
            print(f"  [ok] {net_id}: 写入 {len(final_rules)} 跳过 {skipped} 新建 {created_in_this_target}")
        except Exception as e:
            print(f"  [error] {net_id}: {e}")
            results.append({
                "network_id": net_id,
                "network_name": t.get("network_name", ""),
                "success": False,
                "error": str(e),
            })

    succeeded = sum(1 for r in results if r["success"])
    batch_id = _record_rollback_batch("full_import", rollback_sites)
    print(f"  汇总: {succeeded}/{len(results)} 成功  batch_id={batch_id}")
    return jsonify({
        "results": results,
        "succeeded": succeeded,
        "total": len(results),
        "batch_id": batch_id,
    })


# ---------------------------------------------------------------------------
# 导入端：对象载荷推断 + 决策应用（MerakiL3FirewallApp 方法补充）
# ---------------------------------------------------------------------------
def _guess_object_payload(self, value: str, name: str) -> Dict:
    """根据值的形态自动推断对象的 category/type 与承载字段"""
    v = value.strip()
    # FQDN（含字母且非纯 IP/掩码）
    if re.fullmatch(r"[a-zA-Z0-9.\-]+\.[a-zA-Z]{2,}", v) and "/" not in v:
        return {"name": name, "category": "network", "type": "fqdn", "fqdn": v}
    # CIDR
    if "/" in v:
        return {"name": name, "category": "network", "type": "cidr", "cidr": v}
    # 单 IP（host）
    if re.fullmatch(r"\d{1,3}(\.\d{1,3}){3}", v):
        return {"name": name, "category": "network", "type": "cidr", "cidr": f"{v}/32"}
    # 兜底当 fqdn
    return {"name": name, "category": "network", "type": "fqdn", "fqdn": v}


def _apply_import_segment(self, raw_seg: str, res_seg: str, index: Dict,
                          value_to_new_objid: Dict[str, str],
                          decisions: Dict,
                          vlan_map: Optional[Dict[str, str]] = None,
                          vlan_passthrough: bool = False) -> Optional[str]:
    """
    应用决策，返回最终 cidr 段。返回 None 表示该规则需跳过。
    优先级：VLAN透传/映射 > 新建对象映射 > 原始匹配 > 决策处理。
    """
    # VLAN 引用
    vlan_ref = classify_vlan_ref(raw_seg)
    if vlan_ref is not None:
        if vlan_passthrough:
            # 增量合并：原样透传
            return raw_seg
        tag, _suffix = vlan_ref
        vm = vlan_map or {}
        if tag in vm:
            return vm[tag]
        # VLAN 未映射 → 走决策（key 用 VLAN 原始段，便于决策面板定位）
        key = raw_seg
        dec = decisions.get(key, {})
        action = dec.get("action", "skip")
        if action == "skip":
            return None
        # literal：用决策里手动填的子网（new_name 存放用户填写的 cidr）
        return dec.get("new_name") or key

    kind, _ = classify_ref_segment(raw_seg)
    if kind == "literal":
        return raw_seg  # 字面值

    # 先尝试直接匹配（之前预检可能已能匹配）
    final, _ = match_segment_for_import(raw_seg, res_seg, index, vlan_map, vlan_passthrough)
    if final is not None:
        return final

    # 匹配失败 → 用决策
    _, val = parse_resolved_segment(res_seg)
    key = val or raw_seg
    dec = decisions.get(key, {})
    action = dec.get("action", "literal")

    if action == "create":
        if key in value_to_new_objid:
            return f"OBJ({value_to_new_objid[key]})"
        # 创建可能失败，回退字面值
        return key
    if action == "skip":
        return None
    # literal
    return key


# 挂载为类方法（避免重写整个类）
MerakiL3FirewallApp._guess_object_payload = _guess_object_payload
MerakiL3FirewallApp._apply_import_segment = _apply_import_segment


# ===========================================================================
# 启动
# ===========================================================================
if __name__ == "__main__":
    print("=" * 60)
    print("Meraki L3 防火墙规则导出/导入 Web 工具")
    print(f"BASE_URL = {BASE_URL}")
    print("=" * 60)
    try:
        client = get_client()
    except ValueError as e:
        print(f"\n❌ 启动失败: {e}")
        print("请在 .env 文件中配置 MERAKI_API_KEY 后重试。")
        raise SystemExit(1)

    print(f"\n✅ 启动成功，浏览器访问: http://127.0.0.1:{FLASK_PORT}\n")
    flask_app.run(host="127.0.0.1", port=FLASK_PORT, debug=False)
