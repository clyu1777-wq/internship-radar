# -*- coding: utf-8 -*-
"""实习雷达 · 本地每日监控
每天由计划任务运行:抓取各招聘源 → 与 state.json 中已知岗位 diff → 把结果写进
radar.html 右下角「每日盯梢」面板(MONITOR:START/END 标记之间)。
发布到网页由 run_daily.ps1 里的 claude 步骤完成,本脚本只负责抓取与渲染。
任何单个源失败都不会中断整体;失败源会列在面板的 ⚠ 提示里。
"""
import json
import re
import gzip
import html as html_mod
import datetime
import urllib.request
import urllib.error
import xml.etree.ElementTree as ET
from pathlib import Path

BASE = Path(__file__).parent
STATE_FILE = BASE / "state.json"
REPORT_FILE = BASE / "report.json"
RADAR_FILE = BASE / "radar.html"
SITE_DIR = BASE / "_site"          # GitHub Pages 发布目录(只放 index.html)
FOUND_FILE = BASE / "found.json"   # 累计发现日志:每天追加,永不覆盖
FOUND_RENDER_MAX = 150             # 正文累计板块最多渲染的条数(最新在上)
# 面板精简:只在浮窗里显示前几个,完整列表在正文「监控累计发现」板块

UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"
TIMEOUT = 40

MAX_DISPLAY = 6

# ---- 相关性筛选:只保留「游戏策划 / FDE / 相邻技术」角色,过滤法务/财会/市场/HR 等无关岗 ----
# ROLE = 目标角色(中英双语);LEVEL = 早期职业信号(实习/校招/应届/new grad 等)
ROLE = re.compile(
    # 游戏策划族
    r"策划|关卡|数值|玩法|战斗设计|叙事|剧情|文案|编剧|游戏设计|游戏制作|制作人|交互设计|体验设计|系统策划"
    r"|game\s*design|level\s*design|systems?\s*design|gameplay|narrative|combat\s*design|technical\s*design"
    r"|game\s*produc|world\s*design|encounter\s*design|quest\s*design|content\s*design|ux\s*design|product\s*design|experience\s*design"
    # 游戏运营族(用户追加)
    r"|运营|发行|用户增长|社区运营|内容运营|活动运营|商业化"
    r"|live[\s-]*ops|liveops|game\s*operations|product\s*operations|player\s*support|community\s*manager"
    # FDE / 解决方案族
    r"|解决方案|交付|售前|实施|技术支持|客户成功|部署|现场工程"
    r"|forward[\s-]*deployed|\bfde\b|solutions?\s*(engineer|architect|consultant|specialist)|deployment\s*strateg"
    r"|customer\s*engineer|sales\s*engineer|implementation|technical\s*consultant|field\s*engineer|applied\s*(ai|engineer)"
    # 软件/AI/产品族(用户的技术+FDE 背景相邻)
    r"|程序|客户端|服务端|引擎|算法|后端|前端|全栈|机器学习|人工智能|大模型|智能体|数据科学|工具开发|技术美术|研发"
    r"|产品经理|产品策划|产品运营|产品设计|产品实习|产品助理|产品专员|产品岗|数据产品|用户体验|增长"
    r"|software\s*(engineer|develop|intern|program|architect)|programmer|back[\s-]*end|front[\s-]*end|full[\s-]*stack"
    r"|machine\s*learning|deep\s*learning|\bml\b|\bnlp\b|ai\s*(engineer|builder|developer)|generative\s*ai|gen[\s-]?ai|\bllm\b|\brobotics?\b"
    r"|research\s*(engineer|intern|scientist|associate)|applied\s*(scientist|research)"
    r"|technical\s*program\s*manager|product\s*manage|\bapm\b|gameplay\s*engineer|engine\s*(programmer|engineer)"
    r"|technical\s*(support|advisor|consult)|technology\s*consult|solutions?\s*consult"
    r"|tools?\s*engineer|technical\s*artist|data\s*scien|automation\s*engineer|ai\s*builder|\bux\b|\bagent\b|aigc"
    # AI 各种方向(用户是 AI 工具背景,这些都想要;注意只匹配 AI+具体名词,不匹配「AI向/AI业务/AI方向」以免带进美术/法务/营销)
    r"|AI\s*产品|AI\s*应用|AI\s*创新|AI\s*平台|AI\s*工具|AI\s*基建|AI\s*研发|AI\s*虚拟人|AI\s*系统|游戏\s*AI",
    re.I)
LEVEL = re.compile(
    r"实习|校招|校园招聘|应届|培养生|管培"
    r"|\bintern(ship)?s?\b|\bco[\s-]?op\b|university|new[\s-]?grad|graduate\s*program|early[\s-]?career|apprentic|student|trainee|\bresiden|campus",
    re.I)


# 中国游戏公司:渠道已是校招/实习,且绝大多数岗位都与游戏/技术/AI/产品相关,
# 所以用「黑名单」——默认全要,只排除明确无关的职能(法务/财务/HR/行政/市场/采购/美术/音频等),
# 这样任何叫法奇怪但对口的岗(如「AI产品实习生」「游戏AI研发」「UX设计」)都不会被漏掉。
BLACKLIST_CN = re.compile(
    r"法务|法律|合规|内审|风险控制"
    r"|财务|财会|会计|税务|审计|出纳"
    r"|人力资源|人事|招聘|HRBP|员工关系|薪酬|绩效|培训师"
    r"|行政|前台|文秘|党建|工会|后勤"
    r"|市场营销|品牌|公关|媒介"
    r"|采购|供应链|仓储|物流|物业|资产管理"
    r"|投资|融资|战投|证券"
    r"|美术|原画|概念设计|建模师|次世代|绑定师|动画师|插画|视觉设计|平面设计|美宣"
    r"|音频|音效|作曲|编曲|配音|录音|声优|音乐设计",
    re.I)


def relevant(title):
    """美国/通用源:板子极多元(军工/硬件/后台各种都有),用白名单精准命中目标角色 + 早期职业"""
    return bool(ROLE.search(title)) and bool(LEVEL.search(title))


def relevant_cn(title):
    """中国校招/实习渠道源:黑名单模式,默认全要,只剔除明确无关职能"""
    return not bool(BLACKLIST_CN.search(title))


# ================= 档案资格判定层 =================
# 用户 = 2029 届本科在读,只找【实习】(暑期/日常),不要全职应届/社招,也不要要求硕博的岗。
# 每个岗尽量读正文(fetcher 已把正文塞进 _body,把"实习/全职"轨道塞进 _track,学历塞进 _edu)。
# 判定三档:drop(有明确证据不符→删)/ flag(拿不准→留着标⚠️)/ ok(合格→正常显示)。
# 铁律:只在有正面证据时 drop;读不到正文或含糊,一律 flag 保留,绝不误删。
GRAD_YEAR = 2029

INTERN_MARK = re.compile(r"实习|\bintern(ship)?s?\b|\bco[\s-]?op\b|日常实习", re.I)
FULLTIME_MARK = re.compile(
    r"培训生|管培|管理培训生|储备干部|储备人才|统招|校招正式|正式批"
    r"|\bnew\s*grad\b|newgrad|new\s+graduate|graduate\s+(analyst|engineer|developer|programme|program\b|scheme|rotational)"
    r"|full[\s-]?time\s+new", re.I)
EXP_TITLE = re.compile(r"社招|资深|高级|\bsenior\b|\bstaff\b|\bprincipal\b|\blead\b|专家|经理(?!助理)|总监|\bdirector\b|\bmanager\b(?!\s*intern)", re.I)
EXP_BODY = re.compile(r"\d+\s*年.{0,6}(经验|工作经验|以上)|(\d+)\+?\s*years?\s+of\s+(work\s+|relevant\s+)?experience", re.I)
GRAD_ONLY = re.compile(
    r"硕士及以上|研究生及以上|硕士研究生及以上|(仅|限)(招)?(硕士|研究生|博士)"
    r"|(ms|m\.s\.?|master'?s?)\s+or\s+ph\.?d|pursuing\s+(a\s+)?(an\s+)?(ms\b|m\.s|master|ph\.?d|doctoral)"
    r"|enrolled\s+in\s+(a\s+)?(ph\.?d|master'?s?)\s+(program|degree)|(ph\.?d|master'?s?)\s+program"
    r"|(ph\.?d|博士)\b", re.I)
BACHELOR_OK = re.compile(r"本科|学士|\bbachelor|undergrad|大专|专科|副学士", re.I)
# 明写"及以后 / or later"才算届别放开;单纯"在读/currently enrolled"不算(后面往往紧跟具体届别窗口)
OPEN_UP = re.compile(r"及以后|及之后|或以后|以后.{0,4}毕业|不限届别|不限年级|不限毕业|or\s+later|and\s+beyond|onwards?", re.I)
# 无明确年份窗口时,这些"在校生"信号才用来判 ok
ENROLLED = re.compile(
    r"在校(生|学生|大学生)|欢迎低年级|current\s+student|currently\s+enrolled"
    r"|academic\s+term\s+remaining|remaining\s+after\s+the\s+internship|return(ing)?\s+to\s+school", re.I)
DISABILITY = re.compile(r"残障|残疾|disabilit|people\s+with\s+disab|ignite\s+program", re.I)
MASTER_PREF = re.compile(r"硕士优先|研究生优先|master'?s?\s+(degree\s+)?(is\s+)?preferred|prefer\w*\s+(a\s+)?(master|ph\.?d)", re.I)


def _plain(s):
    """去 HTML 标签、还原实体,得到可做正则的纯文本"""
    if not s:
        return ""
    s = re.sub(r"<[^>]+>", " ", str(s))
    return html_mod.unescape(s)


def grad_verdict(text):
    """从正文里找毕业届别窗口。返回 ok/drop/unknown。只在有明确年份窗口、且最晚届别早于用户、
    又没写"及以后/or later"时才 drop。绝不凭"在读"就判——那句后面往往紧跟具体届别限制。"""
    if not text:
        return "unknown"
    years = set()
    for m in re.finditer(r"(20[2-3]\d)\s*届", text):
        years.add(int(m.group(1)))
    for m in re.finditer(r"毕业[^。;\n]{0,16}?(20[2-3]\d)", text):
        years.add(int(m.group(1)))
    for m in re.finditer(r"(20[2-3]\d)\s*年\s*\d{0,2}\s*月?[^。;\n]{0,8}?毕业", text):
        years.add(int(m.group(1)))
    for m in re.finditer(r"graduat\w*[^.;\n]{0,60}?(20[2-3]\d)(?:[^.;\n]{0,40}?(20[2-3]\d))?", text, re.I):
        years.add(int(m.group(1)))
        if m.group(2):
            years.add(int(m.group(2)))
    for m in re.finditer(r"(20[2-3]\d)[^.;\n]{0,30}?(graduat|conferral|degree\s+complet)", text, re.I):
        years.add(int(m.group(1)))
    years = {y for y in years if 2024 <= y <= 2032}
    if years:
        if OPEN_UP.search(text):     # "2027届及以后" → 放开
            return "ok"
        if max(years) < GRAD_YEAR:   # 有界窗口,最晚也早于用户毕业年 → 明确不符
            return "drop"
        return "ok"
    if ENROLLED.search(text):        # 无年份窗口但明说在校生/还需返校 → 放行
        return "ok"
    return "unknown"


def classify(job, is_cn):
    """返回 (decision, flag)。decision ∈ {'drop','flag','ok'}"""
    title = job.get("title", "") or ""
    body = _plain(job.get("_body", "") or "")
    track = job.get("_track")
    edu = job.get("_edu", "") or ""
    text = title + "\n" + body + "\n" + edu

    # 1) 实习 vs 全职/社招 轨道
    if track == "fulltime":
        return "drop", "全职应届/校招正式"
    if track != "intern" and not INTERN_MARK.search(title):
        if FULLTIME_MARK.search(title + " " + body):
            return "drop", "全职应届/校招正式"
        if EXP_TITLE.search(title):
            return "drop", "资深/社招岗"
        if EXP_BODY.search(body):
            return "drop", "社招·要求工作经验"

    # 2) 学历门槛(标题博士 / 正文仅收硕博)
    if re.search(r"\bph\.?d\b|博士", title, re.I):
        return "drop", "要求博士在读"
    if GRAD_ONLY.search(text) and not BACHELOR_OK.search(text):
        return "drop", "要求硕士/博士在读"

    # 3) 毕业届别窗口
    if grad_verdict(text) == "drop":
        return "drop", "届别不符(需更早毕业)"

    # 4) 留着但标注 ⚠️ 的情形
    if DISABILITY.search(title):   # 只看标题:残障专项会写在职位名里;正文里的多是 EEO 平权声明,不算
        return "flag", "残障包容专项(另一条资格轴)"
    if MASTER_PREF.search(text):
        return "flag", "正文写明偏好硕士"
    if not body:
        if re.search(r"research\s+(intern|scientist)|研究员", title, re.I):
            return "flag", "研究岗·常要研究生,正文未抓到"
        if is_cn and track is None and not INTERN_MARK.search(title):
            return "flag", "校招/实习待确认(正文未抓到)"
        if track is None and not INTERN_MARK.search(title):
            return "flag", "资格未核实(正文未抓到)"
    if job.get("_flag"):   # fetcher 给的定向提示(如腾讯青云/应届实习届别待核)
        return "flag", job["_flag"]
    return "ok", ""


CN_TYPES = {"tencent", "mihoyo", "netease_campus", "leihuo", "feishu", "lingxi", "moka"}


# ---- 岗位归类(仅用于网页分组展示):适合我的五类 vs 其他 ----
CAT_RULES = [
    ("FDE", r"解决方案|交付|forward\s*deployed|\bfde\b|solutions?\s*(engineer|architect|consultant|specialist)"
            r"|deployment\s*strateg|技术咨询|技术支持|实施|售前|customer\s*engineer|sales\s*engineer|field\s*engineer"
            r"|technical\s*(support|consult)|technology\s*consult"),
    ("运营", r"运营|发行|liveops|live[\s-]?ops|game\s*operation|社区|用户增长|增长|商业化|player\s*support|community"),
    ("策划", r"策划|关卡|数值|叙事|剧情|文案|编剧|玩法|战斗设计|game\s*design|level\s*design|systems?\s*design"
            r"|narrative|gameplay\s*design|encounter|quest|content\s*design|交互设计|体验设计|制作人|game\s*produc|world\s*design|ux\s*design"),
    ("AI", r"\bAI\b|AI产品|AI应用|AI平台|AI工具|AI基建|算法|大模型|大语言模型|\bagent\b|agentic|aigc|机器学习|machine\s*learning"
           r"|\bml\b|\bnlp\b|\bllm\b|深度学习|deep\s*learning|智能体|多模态|生成式|generative|research\s*(intern|scientist)"
           r"|数据科学|data\s*scien|虚拟人|具身|world\s*model|世界模型"),
    ("产品", r"产品经理|产品运营|产品策划|产品实习|产品专员|product\s*manage|product\s*manager|\bapm\b|\bpm\b|产品设计|数据产品"),
    ("软件", r"程序|客户端|服务端|引擎|后端|前端|全栈|开发|工程师|软件|software|engineer|develop|programmer"
            r"|back[\s-]?end|front[\s-]?end|full[\s-]?stack|测试|\btest\b|\bqa\b|\bdata\b|技术美术|technical\s*artist|tools?|运维|devops|architect"),
]
CAT_COMPILED = [(n, re.compile(p, re.I)) for n, p in CAT_RULES]
SUITABLE_CATS = {"FDE", "运营", "策划", "AI", "产品"}


def categorize(title, flag):
    """返回 (类别, 是否'适合我的')。带 flag(拿不准)的一律归其他。"""
    cat = "边缘"
    for name, rx in CAT_COMPILED:
        if rx.search(title or ""):
            cat = name
            break
    suit = (cat in SUITABLE_CATS) and not flag
    return cat, suit


def http2(url, method="GET", body=None, headers=None):
    """返回 (text, response_headers)"""
    h = {"User-Agent": UA, "Accept": "application/json", "Accept-Encoding": "gzip"}
    if headers:
        h.update(headers)
    data = None
    if body is not None:
        data = body.encode("utf-8") if isinstance(body, str) else json.dumps(body, ensure_ascii=False).encode("utf-8")
        h.setdefault("Content-Type", "application/json")
    req = urllib.request.Request(url, data=data, headers=h, method=method)
    with urllib.request.urlopen(req, timeout=TIMEOUT) as r:
        raw = r.read()
        if r.headers.get("Content-Encoding", "").lower() == "gzip" or raw[:2] == b"\x1f\x8b":
            raw = gzip.decompress(raw)
        return raw.decode("utf-8", errors="replace"), r.headers


def http(url, method="GET", body=None, headers=None):
    return http2(url, method, body, headers)[0]


def _cookies_from(resp_headers):
    vals = resp_headers.get_all("Set-Cookie") or []
    return "; ".join(v.split(";")[0] for v in vals if "=" in v)


# ---------------- fetchers:每个返回 [{id, title, url}] (已按关键词过滤) ----------------

def f_greenhouse(src):
    data = json.loads(http(f"https://boards-api.greenhouse.io/v1/boards/{src['board']}/jobs?content=true"))
    return [{"id": str(j["id"]), "title": j["title"].strip(), "url": j["absolute_url"],
             "_body": _plain(j.get("content", ""))}
            for j in data.get("jobs", []) if relevant(j["title"])]


def f_lever(src):
    data = json.loads(http(f"https://api.lever.co/v0/postings/{src['org']}?mode=json"))
    out = []
    for j in data:
        if not relevant(j.get("text", "")):
            continue
        body = " ".join([j.get("descriptionPlain", ""), j.get("additionalPlain", ""),
                         _plain(json.dumps(j.get("lists", []), ensure_ascii=False))])
        out.append({"id": j["id"], "title": j["text"].strip(), "url": j["hostedUrl"], "_body": body})
    return out


def f_ashby(src):
    data = json.loads(http(f"https://api.ashbyhq.com/posting-api/job-board/{src['org']}"))
    return [{"id": j["id"], "title": j["title"].strip(), "url": j.get("jobUrl", ""),
             "_body": j.get("descriptionPlain", ""),
             "_track": "intern" if "intern" in str(j.get("employmentType", "")).lower() else ("fulltime" if j.get("employmentType") else None)}
            for j in data.get("jobs", []) if relevant(j.get("title", ""))]


def f_workday(src):
    out, seen = [], set()
    detail_base = src["url"].rsplit("/jobs", 1)[0]  # …/{tenant}/{site}
    for offset in range(0, src.get("pages", 3) * 20, 20):
        body = {"limit": 20, "offset": offset, "searchText": src.get("search", "intern"), "appliedFacets": {}}
        data = json.loads(http(src["url"], "POST", body))
        posts = data.get("jobPostings", [])
        if not posts:
            break
        for j in posts:
            title = (j.get("title") or "").strip()
            path = j.get("externalPath", "")
            jid = (j.get("bulletFields") or [path])[0] or path
            if jid in seen or not title:
                continue
            seen.add(jid)
            if not relevant(title):
                continue
            jd = ""
            try:  # 取正文详情(判定学历/届别),失败则留空→分类器会标 ⚠️ 而非误删
                dj = json.loads(http(detail_base + path))
                jd = _plain((dj.get("jobPostingInfo") or {}).get("jobDescription", ""))
            except Exception:
                pass
            out.append({"id": str(jid), "title": title, "url": src["job_base"] + path, "_body": jd})
    return out


def f_ms_pcsx(src):
    data = json.loads(http("https://apply.careers.microsoft.com/api/pcsx/search?domain=microsoft.com&query=intern&location=&start=0"))
    out = []
    for j in (data.get("data", {}) or {}).get("positions", []):
        title = (j.get("name") or j.get("title") or "").strip()
        jid = str(j.get("id") or j.get("jobId") or j.get("displayJobId") or "")
        url = j.get("canonicalPositionUrl") or j.get("positionUrl") or j.get("applyUrl") or \
            (f"/careers/job/{jid}" if jid else "")
        if url.startswith("/"):  # 接口有时给相对路径,补成绝对地址
            url = "https://apply.careers.microsoft.com" + url
        if title and jid and relevant(title):
            out.append({"id": jid, "title": title, "url": url})
    return out


def f_phenom_widgets(src):
    data = json.loads(http(src["url"], "POST", src["body"]))
    out = []
    for j in ((data.get("refineSearch", {}) or {}).get("data", {}) or {}).get("jobs", []):
        title = (j.get("title") or "").strip()
        jid = str(j.get("jobId") or j.get("reqId") or j.get("jobSeqNo") or "")
        url = j.get("applyUrl") or (src.get("job_url_prefix", "") + jid)
        if title and jid and relevant(title):
            out.append({"id": jid, "title": title, "url": url})
    return out


def f_ea_rss(src):
    xml = http("https://jobs.ea.com/en_US/careers/SearchJobs/intern/feed/?jobRecordsPerPage=100&",
               headers={"Accept": "application/rss+xml, application/xml, */*"})
    root = ET.fromstring(xml)
    out = []
    for item in root.iter("item"):
        title = (item.findtext("title") or "").strip()
        link = (item.findtext("link") or "").strip()
        jid = link.rstrip("/").split("/")[-1] or link
        if title and relevant(title):
            out.append({"id": jid, "title": title, "url": link})
    return out


def f_riot(src):
    page = http("https://www.riotgames.com/en/work-with-us/jobs", headers={"Accept": "text/html"})
    jobs = []
    for raw in re.findall(r'data-props="([^"]+)"', page):
        try:
            props = json.loads(html_mod.unescape(raw))
        except Exception:
            continue
        cand = props.get("jobs") if isinstance(props, dict) else None
        if isinstance(cand, list) and len(cand) > len(jobs):
            jobs = cand
    if not jobs:
        raise RuntimeError("含 jobs 数组的 data-props 未找到,页面结构可能已改版")
    out = []
    for j in jobs:
        title = (j.get("title") or j.get("name") or "").strip()
        url = j.get("url") or j.get("link") or ""
        if url and url.startswith("/"):
            url = "https://www.riotgames.com/en" + url
        jid = str(j.get("internalId") or url or title)
        if title and relevant(title):
            out.append({"id": jid, "title": title, "url": url})
    return out


def f_amazon(src):
    data = json.loads(http("https://www.amazon.jobs/en/search.json?base_query=intern&result_limit=50&offset=0&sort=recent"))
    out = []
    for j in data.get("jobs", []):
        title = (j.get("title") or "").strip()
        jid = str(j.get("id_icims") or j.get("id") or "")
        url = "https://www.amazon.jobs" + (j.get("job_path") or "")
        if title and jid and relevant(title):
            body = " ".join([j.get("basic_qualifications", "") or "", j.get("preferred_qualifications", "") or "",
                             j.get("description", "") or ""])
            out.append({"id": jid, "title": title, "url": url, "_body": body,
                        "_track": "intern" if j.get("is_intern") or j.get("university_job") else None})
    return out


def f_apple(src):
    page = http("https://jobs.apple.com/en-us/search?search=intern&sort=newest", headers={"Accept": "text/html"})
    m = re.search(r'__staticRouterHydrationData\s*=\s*JSON\.parse\("((?:[^"\\]|\\.)*)"\)', page)
    if not m:
        raise RuntimeError("hydration 数据未找到,页面结构可能已改版")
    raw = m.group(1).encode("utf-8").decode("unicode_escape")
    data = json.loads(raw)
    results = []
    def walk(node):
        if isinstance(node, dict):
            if "searchResults" in node and isinstance(node["searchResults"], list):
                results.extend(node["searchResults"])
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)
    walk(data)
    out = []
    for j in results:
        title = (j.get("postingTitle") or j.get("title") or "").strip()
        jid = str(j.get("positionId") or j.get("id") or "")
        slug = j.get("transformedPostingTitle") or ""
        url = f"https://jobs.apple.com/en-us/details/{jid}/{slug}" if jid else ""
        if title and jid and relevant(title):
            out.append({"id": jid, "title": title, "url": url})
    return out


# ---------------- 中国区与其他站点 ----------------

def f_tencent(src):
    """腾讯 join.qq.com 校招门户(实测 800+ 岗)"""
    out, page = {}, 1
    hdr = {"Referer": "https://join.qq.com/post.html", "Origin": "https://join.qq.com"}
    while page <= 12:
        body = {"pageIndex": page, "pageSize": 100}
        if src.get("keyword"):  # 收窄到游戏,排除投资/物业/硬件等非游戏岗
            body["keyword"] = src["keyword"]
        data = json.loads(http("https://join.qq.com/api/v1/position/searchPosition", "POST", body, hdr))
        lst = (data.get("data") or {}).get("positionList") or []
        if not lst:
            break
        before = len(out)
        for j in lst:
            title = (j.get("positionTitle") or "").strip()
            jid = str(j.get("postId") or j.get("id") or "")
            label = j.get("recruitLabelName") or ""   # 日常实习 / 应届实习 / 实习生 青云计划 / 应届毕业生 / …培训生
            track, hint = None, ""
            if "实习" in label:
                track = "intern"
                if "日常实习" not in label:  # 日常实习=面向全体在校生不卡届别;青云/应届实习多面向2027-2028届
                    hint = "青云/应届实习·可能限2027-2028届,投前核毕业届别"
            elif "毕业生" in label or "培训生" in label:
                track = "fulltime"
            if jid and title:
                out[jid] = {"id": jid, "title": title, "_track": track, "_flag": hint,
                            "url": f"https://join.qq.com/post_detail.html?postid={jid}"}
        total = (data.get("data") or {}).get("count") or 0
        if len(out) == before or (total and len(out) >= total):
            break
        page += 1
    return [j for j in out.values() if relevant_cn(j["title"])]


def f_mihoyo(src):
    """米哈游 ATS 公开列表接口(hireType 1=校招通道)"""
    out, page = {}, 1
    hdr = {"Referer": "https://jobs.mihoyo.com/", "Origin": "https://jobs.mihoyo.com"}
    while page <= 8:
        data = json.loads(http("https://ats.openout.mihoyo.com/ats-portal/v1/job/list", "POST",
                               {"pageNo": page, "pageSize": 100, "channelDetailIds": [1], "hireType": 1}, hdr))
        lst = (data.get("data") or {}).get("list") or []
        if not lst:
            break
        before = len(out)
        for j in lst:
            title = (j.get("title") or "").strip()
            jid = str(j.get("id") or "")
            nature = j.get("jobNature") or ""   # '实习' / '全职'
            track = "intern" if nature == "实习" else ("fulltime" if nature == "全职" else None)
            if jid and title:
                out[jid] = {"id": jid, "title": title, "_track": track,
                            "_body": j.get("jobSummary") or "",
                            "url": f"https://jobs.mihoyo.com/#/campus/position/{jid}"}
        total = (data.get("data") or {}).get("total") or 0
        if len(out) == before or (total and len(out) >= total):
            break
        page += 1
    return [j for j in out.values() if relevant_cn(j["title"])]


def f_netease_campus(src):
    """网易互娱 2027 校招(projectId=102)"""
    out, page = {}, 1
    while page <= 8:
        data = json.loads(http(f"https://campus.game.163.com/api/campuspc/position/getJobList?projectId=102&pageIndex={page}&pageSize=100"))
        lst = (data.get("data") or {}).get("list") or []
        if not lst:
            break
        before = len(out)
        for j in lst:
            title = (j.get("positionName") or "").strip()
            jid = str(j.get("id") or "")
            if jid and title:
                out[jid] = {"id": jid, "title": title,
                            "_body": (j.get("positionDescription") or "") + " " + (j.get("positionRequirement") or ""),
                            "url": "https://campus.game.163.com/app/job/position?id=102"}
        if len(out) == before:
            break
        page += 1
    return [j for j in out.values() if relevant_cn(j["title"])]


def f_leihuo(src):
    """网易雷火 日常实习列表"""
    out, page = {}, 1
    while page <= 12:
        data = json.loads(http(f"https://xiaozhao.leihuo.netease.com/api/new/v3/normal_intern/job/list?pageIndex={page}&pageSize=100",
                               headers={"Referer": "https://leihuo.163.com/campus/"}))
        lst = (data.get("data") or {}).get("list") or []
        if not lst:
            break
        before = len(out)
        for j in lst:
            title = (j.get("positionName") or "").strip()
            jid = str(j.get("id") or "")
            if jid and title:
                out[jid] = {"id": jid, "title": title, "_track": "intern",
                            "_body": (j.get("description") or "") + " " + (j.get("requirement") or ""),
                            "_edu": j.get("reqEducationName") or "",
                            "url": "https://leihuo.163.com/campus/#/dailyIntern"}
        if len(out) == before:
            break
        page += 1
    # 雷火板全部是实习岗,按角色筛出策划/技术相关
    return [j for j in out.values() if relevant_cn(j["title"])]


def f_feishu(src):
    """飞书招聘门户(库洛/字节/智谱/莉莉丝):两步 CSRF + 搜索接口"""
    host = src["host"]
    tok_body, hdrs = http2(f"https://{host}/api/v1/csrf/token?portal_entrance=1", "POST", "{}",
                           headers={"Referer": src["referer"]})
    cookies = _cookies_from(hdrs)
    token = (json.loads(tok_body).get("data") or {}).get("token") or ""
    if not token:
        raise RuntimeError("csrf token 为空,飞书门户流程可能已变更")
    hdr = {"Cookie": cookies, "x-csrf-token": token, "Referer": src["referer"]}
    hdr.update(src.get("extra_headers", {}))
    out, offset = {}, 0
    while offset <= 900:
        body = {"keyword": src.get("keyword", ""), "limit": 100, "offset": offset,
                "job_category_id_list": [], "tag_id_list": [], "location_code_list": [],
                "subject_id_list": [], "recruitment_id_list": [], "portal_type": src.get("portal_type", 3),
                "job_function_id_list": [], "storefront_id_list": [], "portal_entrance": 1}
        data = json.loads(http(f"https://{host}/api/v1/search/job/posts?portal_entrance=1", "POST", body, hdr))
        lst = (data.get("data") or {}).get("job_post_list") or []
        if not lst:
            break
        before = len(out)
        for j in lst:
            title = (j.get("title") or "").strip()
            jid = str(j.get("id") or "")
            if jid and title:
                out[jid] = {"id": jid, "title": title,
                            "_body": (j.get("description") or "") + " " + (j.get("requirement") or ""),
                            "url": f"https://{host}/{src['path']}/position/{jid}/detail"}
        total = (data.get("data") or {}).get("count") or 0
        if len(out) == before or (total and len(out) >= total):
            break
        offset += 100
    # 无论服务端是否带 keyword,一律按角色对标题二次过滤(服务端 keyword 会命中描述,放进营销等无关岗)
    return [j for j in out.values() if relevant_cn(j["title"])]


def f_lingxi(src):
    """阿里灵犀互娱:经 talent.alibaba.com 集团站,key=灵犀 过滤"""
    page_html, hdrs = http2("https://talent.alibaba.com/", headers={"Accept": "text/html"})
    m = re.search(r'__token__["\'\s:=]+([0-9a-zA-Z_\-]+)', page_html)
    if not m:
        raise RuntimeError("__token__ 未找到,页面结构可能已改版")
    token, cookies = m.group(1), _cookies_from(hdrs)
    out = []
    body = {"channel": "group_official_site", "language": "zh", "batchId": "", "categories": "",
            "deptCodes": [], "key": "灵犀", "pageIndex": 1, "pageSize": 50, "regions": "", "subCategories": ""}
    data = json.loads(http(f"https://talent.alibaba.com/position/search?_csrf={token}", "POST", body,
                           {"Cookie": cookies, "Referer": "https://talent.alibaba.com/off-campus/position-list?lang=zh"}))
    for j in (data.get("content") or {}).get("datas") or []:
        title = (j.get("name") or "").strip()
        jid = str(j.get("id") or "")
        if jid and title:
            out.append({"id": jid, "title": title,
                        "url": f"https://talent.alibaba.com/off-campus/position-detail?positionId={jid}"})
    return [j for j in out if relevant_cn(j["title"])]


def f_roblox(src):
    """Roblox:Next.js RSC 内嵌数据,无 JSON 接口"""
    page = http("https://careers.roblox.com/jobs", headers={"Accept": "text/html"})
    pairs = re.findall(r'\\"heading\\":\\"((?:[^"\\]|\\\\.)*?)\\",\\"href\\":\\"(/jobs/\d+)', page)
    if not pairs:
        raise RuntimeError("RSC 岗位数据未找到,页面结构可能已改版")
    out = []
    for title, path in pairs:
        title = title.encode("utf-8").decode("unicode_escape").strip()
        jid = path.rsplit("/", 1)[-1]
        if relevant(title):
            out.append({"id": jid, "title": title, "url": f"https://careers.roblox.com{path}"})
    return out


def f_moka(src):
    """Moka ATS(鹰角/完美世界):AES-CBC 加密响应,key=响应内 necromancer,IV 平台固定"""
    from base64 import b64decode
    from Crypto.Cipher import AES
    from Crypto.Util.Padding import unpad
    IV = b"de7c21ed8d6f50fe"
    out = {}
    for site in src["site_ids"]:
        page = 1
        while page <= 6:
            raw = json.loads(http(src["api"], "POST",
                                  {"orgId": src["org"], "siteId": site, "page": page, "size": 100,
                                   "locale": "zh-CN", "needStat": True}))
            enc, key = raw.get("data"), raw.get("necromancer")
            if not enc or not key:
                raise RuntimeError("加密信封字段缺失,Moka 接口可能已变更")
            plain = unpad(AES.new(key.encode(), AES.MODE_CBC, IV).decrypt(b64decode(enc)), 16)
            data = json.loads(plain)
            lst = (data.get("data") or {}).get("jobs") or []
            if not lst:
                break
            before = len(out)
            for j in lst:
                title = (j.get("title") or "").strip()
                jid = str(j.get("id") or "")
                comm = str(j.get("commitment") or "")
                track = "intern" if ("实习" in comm or "intern" in comm.lower()) else \
                        ("fulltime" if (j.get("showIsCampus") and "实习" not in (comm + title)) else None)
                if jid and title:
                    out[jid] = {"id": jid, "title": title, "_track": track, "_body": comm,
                                "url": src["page_url"].replace("{site}", str(site))}
            total = ((data.get("data") or {}).get("jobStats") or {}).get("total") or 0
            if len(out) == before or (total and len(out) >= total):
                break
            page += 1
    return [j for j in out.values() if relevant_cn(j["title"])]


def f_google(src):
    """Google Careers:岗位数据内嵌在页面 AF_initDataCallback ds:1 块中,按日期排序取首页新岗"""
    html = http("https://www.google.com/about/careers/applications/jobs/results/?sort_by=date&q=intern",
                headers={"Accept": "text/html"})
    m = re.search(r"AF_initDataCallback\(\{key:\s*'ds:1'.*?data:(\[.*?\]), sideChannel:", html, re.S)
    if not m:
        raise RuntimeError("ds:1 数据块未找到,Google 页面结构可能已改版")
    data = json.loads(m.group(1))
    out = {}

    def walk(node):
        if isinstance(node, list):
            strs = [x for x in node if isinstance(x, str)]
            ids = [x for x in strs if re.fullmatch(r"\d{15,}", x)]
            titles = [x for x in strs if 6 <= len(x) <= 90 and re.search(r"[A-Za-z]", x)
                      and not x.startswith("http") and "/" not in x and "@" not in x]
            if ids and titles:
                out.setdefault(ids[0], titles[0])
            for x in node:
                walk(x)

    walk(data)
    res = []
    for jid, title in out.items():
        title = title.strip()
        if relevant(title):
            res.append({"id": jid, "title": title,
                        "url": f"https://www.google.com/about/careers/applications/jobs/results/{jid}"})
    return res


FETCHERS = {
    "google": f_google,
    "greenhouse": f_greenhouse,
    "lever": f_lever,
    "ashby": f_ashby,
    "workday": f_workday,
    "ms_pcsx": f_ms_pcsx,
    "phenom_widgets": f_phenom_widgets,
    "ea_rss": f_ea_rss,
    "riot": f_riot,
    "amazon": f_amazon,
    "apple": f_apple,
    "tencent": f_tencent,
    "mihoyo": f_mihoyo,
    "netease_campus": f_netease_campus,
    "leihuo": f_leihuo,
    "feishu": f_feishu,
    "lingxi": f_lingxi,
    "roblox": f_roblox,
    "moka": f_moka,
}


def load_sources():
    return json.loads((BASE / "sources.json").read_text(encoding="utf-8"))


def write_site(html_text):
    """把 body-only 的 radar.html 包成可独立托管的完整 HTML → _site/index.html(GitHub Pages)。
    radar.html 是 body-only 母本;Pages/独立托管需要自带 head/body 这层。输出到 monitor.py 同目录的 index.html
    (云端 = 仓库根;因此 GitHub Pages 直接就能发布)。"""
    i = html_text.find("</style>")
    if i != -1:
        i += len("</style>")
        head_part, body_part = html_text[:i], html_text[i:]  # 首个 </style> 前=title+样式,后=正文+脚本
    else:
        head_part, body_part = "", html_text
    doc = ('<!doctype html>\n<html lang="zh-CN">\n<head>\n'
           '<meta charset="utf-8">\n'
           '<meta name="viewport" content="width=device-width, initial-scale=1">\n'
           + head_part + '\n</head>\n<body>\n' + body_part + '\n</body>\n</html>\n')
    (BASE / "index.html").write_text(doc, encoding="utf-8")


def main():
    today = (datetime.datetime.now(datetime.timezone.utc) + datetime.timedelta(hours=8)).date().isoformat()  # 北京时间(云端在UTC跑)
    state = json.loads(STATE_FILE.read_text(encoding="utf-8")) if STATE_FILE.exists() else {}
    sources = load_sources()

    new_jobs, failures, baseline_added, pool_jobs = [], [], 0, []
    for src in sources:
        if not src.get("enabled", True):
            continue
        key, company = src["key"], src["company"]
        jobs, last_err = None, None
        for attempt in range(2):  # 失败自动重试一次,吸收偶发超时/传输中断
            try:
                jobs = FETCHERS[src["type"]](src)
                break
            except Exception as e:
                last_err = e
        if jobs is None:
            st = state.setdefault(key, {"ids": [], "fail_streak": 0})
            st["fail_streak"] = st.get("fail_streak", 0) + 1
            failures.append({"company": company, "error": str(last_err)[:200], "streak": st["fail_streak"]})
            continue
        st = state.setdefault(key, {"ids": [], "fail_streak": 0})
        st["fail_streak"] = 0
        # 档案资格判定:删掉明确不符(全职应届/社招/要研究生/届别不符),拿不准的留着挂 flag
        is_cn = src["type"] in CN_TYPES
        kept = []
        for j in jobs:
            dec, flag = classify(j, is_cn)
            if dec == "drop":
                continue
            kept.append({"id": j["id"], "title": j["title"], "url": j.get("url", ""),
                         "flag": flag if dec == "flag" else ""})
        jobs = kept
        for j in jobs:  # 全部合格岗进候选池(不管新旧),供网页浏览
            pool_jobs.append({"srckey": key, "co": company, "id": j["id"],
                              "title": j["title"], "url": j.get("url", ""), "flag": j.get("flag", "")})
        if not st.get("init"):  # 首次成功运行:建基线,不报新增(即使当天板子为空)
            st["ids"] = [j["id"] for j in jobs]
            st["init"] = True
            baseline_added += len(jobs)
            st["last_ok"] = today
            continue
        known = set(st["ids"])
        for j in jobs:
            if j["id"] not in known:
                new_jobs.append({"company": company, "srckey": key, **j})
        st["ids"] = sorted(known | {j["id"] for j in jobs})
        st["last_ok"] = today

    STATE_FILE.write_text(json.dumps(state, ensure_ascii=False, indent=1), encoding="utf-8")
    REPORT_FILE.write_text(json.dumps(
        {"date": today, "new_jobs": new_jobs, "failures": failures, "baseline_added": baseline_added},
        ensure_ascii=False, indent=1), encoding="utf-8")

    # ---- 大面积失败保护:抓挂太多就别覆盖网页(保留上一版好页面),返回非零码让 run_daily 跳过发布 ----
    enabled_n = len([s for s in sources if s.get("enabled", True)])
    if len(failures) > max(6, enabled_n // 2):
        print(f"MASS-FAIL date={today} failures={len(failures)}/{enabled_n} - 保留上一版页面, 跳过发布")
        raise SystemExit(2)

    # ---- 组装候选池,注入网页(前端 JS 负责分组/折叠/删除/收藏) ----
    new_uids = {f"{nj['srckey']}:{nj['id']}" for nj in new_jobs}
    pool = []
    for p in pool_jobs:
        uid = f"{p['srckey']}:{p['id']}"
        cat, suit = categorize(p["title"], p["flag"])
        pool.append({"uid": uid, "co": p["co"], "t": p["title"], "u": p["url"],
                     "cat": cat, "suit": bool(suit), "flag": p["flag"], "new": uid in new_uids})
    (BASE / "pool.json").write_text(json.dumps(pool, ensure_ascii=False, indent=1), encoding="utf-8")

    new_suit = sum(1 for x in pool if x["new"] and x["suit"])
    meta = {"date": today, "newCount": new_suit,
            "fails": [f["company"] + (f"(连续{f['streak']}天失败)" if f["streak"] >= 2 else "") for f in failures]}

    def js(obj):  # 内联进 <script> 时防止 </script> 提前闭合
        return json.dumps(obj, ensure_ascii=False).replace("</", "<\\/")

    html_text = RADAR_FILE.read_text(encoding="utf-8")
    html_text = re.sub(r"/\*POOL:START\*/.*?/\*POOL:END\*/",
                       lambda m: "/*POOL:START*/" + js(pool) + "/*POOL:END*/", html_text, flags=re.S)
    html_text = re.sub(r"/\*META:START\*/.*?/\*META:END\*/",
                       lambda m: "/*META:START*/" + js(meta) + "/*META:END*/", html_text, flags=re.S)
    RADAR_FILE.write_text(html_text, encoding="utf-8")
    write_site(html_text)  # 同步产出 _site/index.html 供 GitHub Pages 发布
    print(f"OK date={today} new={len(new_jobs)} new_suit={new_suit} pool={len(pool)} "
          f"baseline={baseline_added} failures={len(failures)}")


if __name__ == "__main__":
    main()
