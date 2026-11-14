// SPDX-License-Identifier: GPL-2.0
/*
 * ask_rw.c — ASK 驱动 v3.1 (5.10 专属优化版)
 * 适配内核: 5.10.246-android12-9 (AArch64)
 */
#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/init.h>
#include <linux/fs.h>
#include <linux/miscdevice.h>
#include <linux/uaccess.h>
#include <linux/ioctl.h>
#include <linux/slab.h>
#include <linux/vmalloc.h>
#include <linux/spinlock.h>
#include <linux/rwsem.h>
#include <linux/sched.h>
#include <linux/sched/mm.h>
#include <linux/sched/task.h>
#include <linux/pid.h>
#include <linux/mm.h>
#include <linux/mm_types.h>
#include <linux/highmem.h>
#include <linux/kprobes.h>
#include <linux/version.h>
#include <linux/errno.h>
#include <linux/string.h>
#include <linux/preempt.h>
#include <linux/page-flags.h>
#include <linux/swap.h>
#include <linux/swapops.h>
#include <linux/bio.h>
#include <linux/blkdev.h>
#include <linux/dcache.h>
#include <linux/path.h>
#include <linux/file.h>
#include <linux/ktime.h>
#include <asm/pgtable.h>
#include <asm/pgalloc.h>
#include <asm/tlbflush.h>
#include <asm/cacheflush.h>
#include <asm/thread_info.h>
#include <asm/sysreg.h>
#include <asm/mmu_context.h>
#include <asm/pgtable-hwdef.h>
#include <asm/memory.h> /* 用于 __va / __pa */

MODULE_LICENSE("GPL");
MODULE_AUTHOR("ASK");
MODULE_DESCRIPTION("ASK v3.1: cross-process R/W for 5.10");
MODULE_VERSION("3.1");

/* 5.10 宏定义 */
#define ASK_ACCESS_OK(a,s) access_ok((a),(s))
#define ASK_KMAP(p)    kmap_atomic(p)
#define ASK_KUNMAP(v)  kunmap_atomic(v)

/* 用户态协议 */
#define ASK_IOC_MAGIC 'A'
#define ASK_MAX_TARGETS 8
#define ASK_BATCH_MAX   256
#define ASK_SCAN_MAX_HITS 256
#define ASK_MODNAME_MAX 64

struct ask_req { __u32 slot; __u32 flags; __u64 remote_va; __u64 local_va;
                 __u64 size; __u32 pid; __u32 _pad; };
#define ASK_F_LINEAR      (1u<<0)
#define ASK_F_TTBR        (1u<<1)
#define ASK_F_WRITE       (1u<<2)
#define ASK_F_FORCE_SWAP  (1u<<3)

struct ask_status { __u32 attached[ASK_MAX_TARGETS]; __s32 pids[ASK_MAX_TARGETS];
                    __u64 pgds[ASK_MAX_TARGETS]; __u64 ttbr0s[ASK_MAX_TARGETS];
                    __u32 map_used; __u32 map_total; __u32 audit_head; };
struct ask_iov { __u64 remote_va; __u64 local_va; __u64 size; __s32 ret; __u32 _pad; };
struct ask_batch_req { __u32 slot; __u32 flags; __u32 count; __u32 _pad;
                       struct ask_iov iov[ASK_BATCH_MAX]; };
struct ask_scan_req { __u32 slot; __u32 flags; __u64 start; __u64 end;
                      __u64 pattern_va; __u32 pattern_len; __u32 max_hits;
                      __u64 hits_va; __u32 hit_count; __u32 _pad; };
struct ask_mod_req { __u32 slot; __u32 _pad; char name[ASK_MODNAME_MAX];
                     __u64 base_out; __u64 size_out; };
struct ask_phys_req { __u64 pa; __u64 local_va; __u64 size; };
struct ask_audit_ent { __u64 ts_ns; __u32 slot; __u32 op; __u64 remote_va;
                       __u64 size; __s32 ret; __u32 _pad; };

#define ASK_IOC_ATTACH      _IOWR(ASK_IOC_MAGIC, 1, struct ask_req)
#define ASK_IOC_DETACH      _IOWR(ASK_IOC_MAGIC, 2, struct ask_req)
#define ASK_IOC_RW          _IOWR(ASK_IOC_MAGIC, 3, struct ask_req)
#define ASK_IOC_STATUS      _IOWR(ASK_IOC_MAGIC, 4, struct ask_req)
#define ASK_IOC_BATCH       _IOWR(ASK_IOC_MAGIC, 5, struct ask_batch_req)
#define ASK_IOC_SCAN        _IOWR(ASK_IOC_MAGIC, 6, struct ask_scan_req)
#define ASK_IOC_MODULE      _IOWR(ASK_IOC_MAGIC, 7, struct ask_mod_req)
#define ASK_IOC_PHYS_READ   _IOWR(ASK_IOC_MAGIC, 8, struct ask_phys_req)
#define ASK_IOC_AUDIT       _IOWR(ASK_IOC_MAGIC, 9, struct ask_audit_ent)

/* 全局符号 */
static unsigned long *g_memstart_addr;
static int (*g_pfn_is_map_memory)(unsigned long);
static int (*g_pfn_valid)(unsigned long);
static unsigned long (*g_arch_copy_to_user)(void __user *, const void *, unsigned long);
static unsigned long (*g_arch_copy_from_user)(void *, const void __user *, unsigned long);
static int (*g_access_process_vm)(struct task_struct *, unsigned long, void *, int, unsigned int);
static struct swap_info_struct **g_swap_info;

static void *ask_ksym(const char *name)
{
#if IS_ENABLED(CONFIG_KPROBES)
    struct kprobe kp = { .symbol_name = "kallsyms_lookup_name" };
    void *fn; int ret = register_kprobe(&kp);
    if (ret) return NULL;
    fn = (void *)kp.addr;
    unregister_kprobe(&kp);
    if (!fn) return NULL;
    return ((void *(*)(const char *))fn)(name);
#else
    return (void *)kallsyms_lookup_name(name);
#endif
}

static int ask_resolve_syms(void)
{
    g_memstart_addr        = (void *)ask_ksym("memstart_addr");
    g_pfn_is_map_memory    = (void *)ask_ksym("pfn_is_map_memory");
    g_pfn_valid            = (void *)ask_ksym("pfn_valid");
    g_arch_copy_to_user    = (void *)ask_ksym("__arch_copy_to_user");
    g_arch_copy_from_user  = (void *)ask_ksym("__arch_copy_from_user");
    g_access_process_vm    = (void *)ask_ksym("access_process_vm");
    g_swap_info            = (void *)ask_ksym("swap_info");
    if (!g_memstart_addr || !g_arch_copy_to_user || !g_arch_copy_from_user) {
        pr_err("ask: 必需符号缺失\n"); return -ENOENT;
    }
    return 0;
}

/* 5.10 标准地址换算 */
static inline u64 ask_phys_to_virt(u64 pa) { return (u64)__va(pa); }

static inline int ask_pfn_ok(u64 pa)
{
    unsigned long pfn = pa >> PAGE_SHIFT;
    if (g_pfn_is_map_memory) return g_pfn_is_map_memory(pfn) ? 1 : 0;
    if (g_pfn_valid)         return g_pfn_valid(pfn) ? 1 : 0;
    return 1;
}

static inline struct page *ask_compound_head(struct page *page)
{
    unsigned long h = READ_ONCE(page->compound_head);
    return (h & 1) ? (struct page *)(h - 1) : page;
}

/* 多目标槽 + 审计环 */
struct ask_target { pid_t pid; struct mm_struct *mm; u64 ttbr0; u32 used; };
static struct ask_target g_tgts[ASK_MAX_TARGETS];
static DEFINE_RWLOCK(g_tgt_lock);

struct ask_audit { u64 ts_ns; u32 slot; u32 op; u64 remote_va; u64 size; s32 ret; u32 _pad; };
static struct ask_audit g_audit[64];
static DEFINE_SPINLOCK(g_audit_lock);
static u32 g_audit_head;

static void ask_audit_log(u32 slot, u32 op, u64 rva, u64 size, s32 ret)
{
    unsigned long flags; u32 idx;
    spin_lock_irqsave(&g_audit_lock, flags);
    idx = g_audit_head++ & 63;
    g_audit[idx].ts_ns = ktime_get_ns();
    g_audit[idx].slot = slot; g_audit[idx].op = op;
    g_audit[idx].remote_va = rva; g_audit[idx].size = size; g_audit[idx].ret = ret;
    spin_unlock_irqrestore(&g_audit_lock, flags);
}

static u64 ask_make_ttbr0(struct mm_struct *mm)
{
    phys_addr_t pgd_pa; u64 asid;
    if (!mm || !mm->pgd) return 0;
    pgd_pa = virt_to_phys(mm->pgd);
    if (!ask_pfn_ok(pgd_pa)) return 0;
    asid = atomic64_read(&mm->context.id) & 0xFFFF;
    return (pgd_pa & 0x0000FFFFFFFFF000ULL) | (asid << 48);
}

static int ask_attach_slot(u32 slot, pid_t pid)
{
    struct pid *pidp; struct task_struct *task; struct mm_struct *mm, *old = NULL; u64 ttbr0;
    if (slot >= ASK_MAX_TARGETS) return -EINVAL;
    pidp = find_get_pid(pid);
    if (!pidp) return -ESRCH;
    task = get_pid_task(pidp, PIDTYPE_PID);
    put_pid(pidp);
    if (!task) return -ESRCH;
    mm = get_task_mm(task);
    put_task_struct(task);
    if (!mm) return -ESRCH;
    ttbr0 = ask_make_ttbr0(mm);
    if (!ttbr0) { mmput(mm); return -EINVAL; }
    write_lock(&g_tgt_lock);
    old = g_tgts[slot].mm;
    g_tgts[slot].pid = pid; g_tgts[slot].mm = mm;
    g_tgts[slot].ttbr0 = ttbr0; g_tgts[slot].used = 1;
    write_unlock(&g_tgt_lock);
    if (old) mmput(old);
    pr_info("ask: slot %u -> pid %d mm %px\n", slot, pid, mm);
    return 0;
}

static void ask_detach_slot(u32 slot)
{
    struct mm_struct *old = NULL;
    if (slot >= ASK_MAX_TARGETS) return;
    write_lock(&g_tgt_lock);
    old = g_tgts[slot].mm; g_tgts[slot].mm = NULL; g_tgts[slot].used = 0;
    write_unlock(&g_tgt_lock);
    if (old) mmput(old);
}

static struct mm_struct *ask_get_mm_slot(u32 slot, u64 *ttbr0_out)
{
    struct mm_struct *mm = NULL;
    if (slot >= ASK_MAX_TARGETS) return NULL;
    read_lock(&g_tgt_lock);
    if (g_tgts[slot].mm && mmget_not_zero(g_tgts[slot].mm)) {
        mm = g_tgts[slot].mm;
        if (ttbr0_out) *ttbr0_out = g_tgts[slot].ttbr0;
    }
    read_unlock(&g_tgt_lock);
    return mm;
}

static pid_t ask_get_pid_slot(u32 slot)
{
    pid_t pid = -1;
    if (slot >= ASK_MAX_TARGETS) return -1;
    read_lock(&g_tgt_lock); pid = g_tgts[slot].pid; read_unlock(&g_tgt_lock);
    return pid;
}

/* 页表走查 */
static u64 ask_walk_va(struct mm_struct *mm, u64 va, void **ptep_out, int *level_out)
{
    pgd_t *pgd; p4d_t *p4d; pud_t *pud; pmd_t *pmd; pte_t *ptep; u64 pa, off;
    if (ptep_out) *ptep_out = NULL; if (level_out) *level_out = 0;
    if (!mm || !mm->pgd || va == 0) return 0;
    pgd = pgd_offset(mm, va); if (pgd_none(*pgd) || !pgd_present(*pgd)) return 0;
    p4d = p4d_offset(pgd, va); if (p4d_none(*p4d) || !p4d_present(*p4d)) return 0;
    pud = pud_offset(p4d, va); if (pud_none(*pud) || !pud_present(*pud)) return 0;
    if (pud_leaf(*pud)) {
        pa = (u64)pud_pfn(*pud) << PAGE_SHIFT; off = va & (PUD_SIZE - 1);
        if (!ask_pfn_ok(pa)) return 0; if (ptep_out) *ptep_out = (void *)pud;
        if (level_out) *level_out = 1; return pa | off;
    }
    pmd = pmd_offset(pud, va); if (pmd_none(*pmd) || !pmd_present(*pmd)) return 0;
    if (pmd_leaf(*pmd)) {
        pa = (u64)pmd_pfn(*pmd) << PAGE_SHIFT; off = va & (PMD_SIZE - 1);
        if (!ask_pfn_ok(pa)) return 0; if (ptep_out) *ptep_out = (void *)pmd;
        if (level_out) *level_out = 2; return pa | off;
    }
    ptep = pte_offset_kernel(pmd, va);
    if (!ptep || pte_none(*ptep) || !pte_present(*ptep)) return 0;
    if (pte_special(*ptep) || pte_protnone(*ptep)) return 0;
#ifdef CONFIG_ARCH_HAS_PTE_DEVMAP
    if (pte_devmap(*ptep)) return 0;
#endif
    pa = (u64)pte_pfn(*ptep) << PAGE_SHIFT; off = va & (PAGE_SIZE - 1);
    if (!ask_pfn_ok(pa)) return 0; if (ptep_out) *ptep_out = (void *)ptep;
    if (level_out) *level_out = 3; return pa | off;
}

static int ask_walk_swap_pte(struct mm_struct *mm, u64 va, pte_t **ptep_out)
{
    pgd_t *pgd; p4d_t *p4d; pud_t *pud; pmd_t *pmd; pte_t *ptep;
    if (!mm || !mm->pgd || !ptep_out) return -EINVAL;
    pgd = pgd_offset(mm, va); if (pgd_none(*pgd)) return -EINVAL;
    p4d = p4d_offset(pgd, va); if (p4d_none(*p4d)) return -EINVAL;
    pud = pud_offset(p4d, va); if (pud_none(*pud) || pud_leaf(*pud)) return -EINVAL;
    pmd = pmd_offset(pud, va); if (pmd_none(*pmd) || pmd_leaf(*pmd)) return -EINVAL;
    ptep = pte_offset_kernel(pmd, va); if (!ptep) return -EINVAL;
    *ptep_out = ptep; return 0;
}

static int ask_still_valid(void *ptep, u64 pa, int level)
{
    if (!ptep) return 0;
    switch (level) {
    case 1: { pud_t v = READ_ONCE(*(pud_t *)ptep); if (!pud_present(v) || !pud_leaf(v)) return 0; return ((u64)pud_pfn(v) << PAGE_SHIFT) == (pa & PUD_MASK); }
    case 2: { pmd_t v = READ_ONCE(*(pmd_t *)ptep); if (!pmd_present(v) || !pmd_leaf(v)) return 0; return ((u64)pmd_pfn(v) << PAGE_SHIFT) == (pa & PMD_MASK); }
    case 3: { pte_t v = READ_ONCE(*(pte_t *)ptep); if (!pte_present(v) || pte_special(v)) return 0; return ((u64)pte_pfn(v) << PAGE_SHIFT) == (pa & PAGE_MASK); }
    default: return 0;
    }
}

/* 映射池 */
#define ASK_SLOT_NR 64
#define ASK_POOL_SIZE (ASK_SLOT_NR * PAGE_SIZE)
struct ask_slot { u64 pa; unsigned long stamp; int in_use; };
static struct vm_struct *g_area;
static pte_t **g_ptes; /* 5.10 此处为 NULL */
static void *g_slot_va[ASK_SLOT_NR];
static struct ask_slot g_slot[ASK_SLOT_NR];
static DEFINE_SPINLOCK(g_slot_lock);
static unsigned long g_stamp;

static pte_t *ask_kernel_pte_of(unsigned long va)
{
    pgd_t *pgd = pgd_offset_k(va); p4d_t *p4d; pud_t *pud; pmd_t *pmd;
    if (pgd_none(*pgd) || !pgd_present(*pgd)) return NULL;
    p4d = p4d_offset(pgd, va); if (p4d_none(*p4d)) return NULL;
    pud = pud_offset(p4d, va); if (pud_none(*pud)) return NULL;
    pmd = pmd_offset(pud, va); if (pmd_none(*pmd)) return NULL;
    return pte_offset_kernel(pmd, va);
}

static int ask_pool_init(void)
{
    int i;
    g_area = alloc_vm_area(ASK_POOL_SIZE); /* 5.10 单参 */
    g_ptes = NULL;
    if (!g_area) return -ENOMEM;
    for (i = 0; i < ASK_SLOT_NR; i++) {
        pte_t *ptep;
        g_slot_va[i] = (void *)((unsigned long)g_area->addr + i * PAGE_SIZE);
        ptep = ask_kernel_pte_of((unsigned long)g_slot_va[i]);
        if (ptep) set_pte(ptep, __pte(0));
        g_slot[i].pa = 0; g_slot[i].stamp = 0; g_slot[i].in_use = 0;
    }
    pr_info("ask: map pool @ %px, %d slots\n", g_area->addr, ASK_SLOT_NR);
    return 0;
}

static void ask_pool_exit(void)
{
    int i;
    if (!g_area) return;
    for (i = 0; i < ASK_SLOT_NR; i++) {
        pte_t *ptep = ask_kernel_pte_of((unsigned long)g_slot_va[i]);
        if (ptep) set_pte(ptep, __pte(0));
        g_slot[i].pa = 0;
    }
    flush_tlb_kernel_range((unsigned long)g_area->addr, (unsigned long)g_area->addr + ASK_POOL_SIZE);
    free_vm_area(g_area); g_area = NULL;
}

static void *ask_map_phys(u64 pa)
{
    unsigned long flags; int i, victim = -1; unsigned long oldest = ~0UL;
    void *va = NULL; pte_t *ptep;
    pa &= PAGE_MASK;
    spin_lock_irqsave(&g_slot_lock, flags);
    for (i = 0; i < ASK_SLOT_NR; i++) {
        if (g_slot[i].pa == pa) { g_slot[i].stamp = ++g_stamp; g_slot[i].in_use++; va = g_slot_va[i]; goto out; }
    }
    for (i = 0; i < ASK_SLOT_NR; i++) if (g_slot[i].pa == 0) { victim = i; break; }
    if (victim < 0) {
        for (i = 0; i < ASK_SLOT_NR; i++) {
            if (g_slot[i].in_use) continue;
            if (g_slot[i].stamp < oldest) { oldest = g_slot[i].stamp; victim = i; }
        }
    }
    if (victim < 0) { pr_warn_ratelimited("ask: pool busy\n"); goto out; }
    va = g_slot_va[victim]; ptep = ask_kernel_pte_of((unsigned long)va);
    if (!ptep) { va = NULL; goto out; }
    set_pte(ptep, pfn_pte(pa >> PAGE_SHIFT, PAGE_KERNEL));
    g_slot[victim].pa = pa; g_slot[victim].stamp = ++g_stamp; g_slot[victim].in_use = 1;
out:
    spin_unlock_irqrestore(&g_slot_lock, flags);
    if (va) flush_tlb_kernel_range((unsigned long)va, (unsigned long)va + PAGE_SIZE);
    return va;
}

static void ask_map_put(void *va)
{
    unsigned long flags; int i;
    if (!va) return;
    spin_lock_irqsave(&g_slot_lock, flags);
    for (i = 0; i < ASK_SLOT_NR; i++) if (g_slot_va[i] == va) { if (g_slot[i].in_use > 0) g_slot[i].in_use--; break; }
    spin_unlock_irqrestore(&g_slot_lock, flags);
}

/* cache 维护 */
static unsigned int g_cache_line = 64;
static void ask_cache_line_init(void)
{
    unsigned long ctr; asm volatile("mrs %0, ctr_el0" : "=r"(ctr));
    g_cache_line = 4UL << ((ctr >> 16) & 0xF); if (!g_cache_line) g_cache_line = 64;
}
static void ask_dc_inval(void *start, unsigned long len)
{
    unsigned long a = (unsigned long)start & ~(unsigned long)(g_cache_line - 1);
    unsigned long end = (unsigned long)start + len;
    for (; a < end; a += g_cache_line) asm volatile("dc ivac, %0" :: "r"(a) : "memory");
    dsb(ish);
}
static void ask_dc_civac(void *start, unsigned long len)
{
    unsigned long a = (unsigned long)start & ~(unsigned long)(g_cache_line - 1);
    unsigned long end = (unsigned long)start + len;
    for (; a < end; a += g_cache_line) asm volatile("dc civac, %0" :: "r"(a) : "memory");
    dsb(ish);
}
static void ask_icache_sync(void *start, unsigned long len)
{
    ask_dc_civac(start, len);
    asm volatile("ic iallu" ::: "memory");
    dsb(ish); isb();
}

/* TTBR 劫持 */
static unsigned long ask_ttbr_read(void *dst, u64 rva, unsigned long len, u64 ttbr0)
{
    unsigned long daif, ret; u64 ttbr1;
    if (!g_arch_copy_from_user || !ttbr0) return len;
    preempt_disable();
    asm volatile("mrs %0, daif" : "=r"(daif));
    asm volatile("msr daifset, #3" ::: "memory");
    ttbr1 = read_sysreg(ttbr1_el1);
    write_sysreg((ttbr0 & 0xFFFF000000000000ULL) | (ttbr1 & 0xFFFFFFFFFFFFULL), ttbr1_el1);
    write_sysreg(ttbr0, ttbr0_el1); isb();
    asm volatile("msr daif, %0" :: "r"(daif) : "memory");
    ret = g_arch_copy_from_user(dst, (const void __user *)(rva & 0xFF7FFFFFFFFFFFFFULL), len);
    asm volatile("msr daifset, #3" ::: "memory");
    ttbr1 = read_sysreg(ttbr1_el1) & 0xFFFFFFFFFFFFULL;
    write_sysreg(ttbr1 - 4096, ttbr0_el1); write_sysreg(ttbr1, ttbr1_el1); isb();
    asm volatile("msr daif, %0" :: "r"(daif) : "memory");
    preempt_enable();
    if (ret) memset((char *)dst + len - ret, 0, ret);
    return ret;
}

static unsigned long ask_ttbr_write(u64 rva, const void *src, unsigned long len, u64 ttbr0)
{
    unsigned long daif, ret; u64 ttbr1;
    if (!g_arch_copy_to_user || !ttbr0) return len;
    preempt_disable();
    asm volatile("mrs %0, daif" : "=r"(daif));
    asm volatile("msr daifset, #3" ::: "memory");
    ttbr1 = read_sysreg(ttbr1_el1);
    write_sysreg((ttbr0 & 0xFFFF000000000000ULL) | (ttbr1 & 0xFFFFFFFFFFFFULL), ttbr1_el1);
    write_sysreg(ttbr0, ttbr0_el1); isb();
    asm volatile("msr daif, %0" :: "r"(daif) : "memory");
    ret = g_arch_copy_to_user((void __user *)(rva & 0xFF7FFFFFFFFFFFFFULL), src, len);
    asm volatile("msr daifset, #3" ::: "memory");
    ttbr1 = read_sysreg(ttbr1_el1) & 0xFFFFFFFFFFFFULL;
    write_sysreg(ttbr1 - 4096, ttbr0_el1); write_sysreg(ttbr1, ttbr1_el1); isb();
    asm volatile("msr daif, %0" :: "r"(daif) : "memory");
    preempt_enable();
    return ret;
}

/* swap 回退（5.10 专属签名） */
static u64 ask_swap_read_direct(swp_entry_t entry, void *dst, u64 off, u64 len)
{
    struct swap_info_struct *si; struct block_device *bdev;
    struct bio *bio; struct page *page; u64 sector; void *kva;
    unsigned int type;
    if (len + off > PAGE_SIZE || !g_swap_info) return 0;
    type = swp_type(entry);
    if (type >= MAX_SWAPFILES) return 0;
    si = g_swap_info[type];
    if (!si) return 0;
    bdev = si->bdev;
    if (!bdev) return 0;
    sector = 8ULL * swp_offset(entry);
    page = alloc_page(GFP_ATOMIC);
    if (!page) return 0;
    /* 5.10 老版 bio_alloc */
    bio = bio_alloc(GFP_ATOMIC, 1);
    if (!bio) { __free_page(page); return 0; }
    bio_set_dev(bio, bdev);
    bio->bi_iter.bi_sector = sector;
    bio_set_op_attrs(bio, REQ_OP_READ, 0);
    if (!bio_add_page(bio, page, PAGE_SIZE, 0)) { bio_put(bio); __free_page(page); return 0; }
    if (submit_bio_wait(bio) != 0) { bio_put(bio); __free_page(page); return 0; }
    bio_put(bio);
    kva = ASK_KMAP(page);
    memcpy(dst, (u8 *)kva + off, len);
    ASK_KUNMAP(kva);
    __free_page(page);
    return len;
}

static int ask_swap_read(struct mm_struct *mm, u64 va, void *dst, u64 len)
{
    pte_t *ptep = NULL; pte_t pte; swp_entry_t entry; u64 off = va & (PAGE_SIZE-1);
    if (ask_walk_swap_pte(mm, va, &ptep)) return -EINVAL;
    pte = READ_ONCE(*ptep);
    if (!is_swap_pte(pte)) return -EINVAL;
    entry = pte_to_swp_entry(pte);
    if (!ask_swap_read_direct(entry, dst, off, len)) return -EIO;
    return 0;
}

/* 写路径 */
static u64 ask_write_direct(struct mm_struct *mm, u64 va, const u8 *src, u64 len)
{
    u64 done = 0;
    while (done < len) {
        u64 off = (va + done) & (PAGE_SIZE - 1); u64 chunk = min_t(u64, PAGE_SIZE - off, len - done);
        void *ptep = NULL; int level = 0; u64 pa; void *kva;
        rcu_read_lock(); pa = ask_walk_va(mm, va + done, &ptep, &level);
        if (!pa || !ask_still_valid(ptep, pa, level)) { rcu_read_unlock(); break; }
        rcu_read_unlock();
        kva = ask_map_phys(pa & PAGE_MASK); if (!kva) break;
        memcpy((char *)kva + off, src + done, chunk);
        ask_dc_civac((char *)kva + off, chunk); ask_map_put(kva); done += chunk;
    }
    return done;
}

static u64 ask_write_anon_cow(struct mm_struct *mm, u64 va, const u8 *src, u64 len)
{
    u64 done = 0;
    while (done < len) {
        u64 off = (va + done) & (PAGE_SIZE - 1); u64 chunk = min_t(u64, PAGE_SIZE - off, len - done);
        void *ptep = NULL; int level = 0; u64 pa; struct page *page, *head; void *kva;
        rcu_read_lock(); pa = ask_walk_va(mm, va + done, &ptep, &level);
        if (!pa || level != 3 || !ask_still_valid(ptep, pa, level)) { rcu_read_unlock(); break; }
        rcu_read_unlock();
        page = pfn_to_page(pa >> PAGE_SHIFT); head = ask_compound_head(page);
        if (!PageAnon(head)) break;
        kva = ask_map_phys(pa & PAGE_MASK); if (!kva) break;
        memcpy((char *)kva + off, src + done, chunk);
        set_page_dirty_lock(head); ask_dc_civac((char *)kva + off, chunk);
        ask_map_put(kva); done += chunk;
    }
    return done;
}

static u64 ask_write_apv(struct mm_struct *mm, u64 va, const u8 *src, u64 len, pid_t pid)
{
    struct pid *pidp; struct task_struct *task; u64 done = 0;
    if (!g_access_process_vm || pid <= 0) return 0;
    pidp = find_get_pid(pid); if (!pidp) return 0;
    task = get_pid_task(pidp, PIDTYPE_PID); put_pid(pidp); if (!task) return 0;
    while (done < len) {
        u64 off = (va + done) & (PAGE_SIZE - 1); u64 chunk = min_t(u64, PAGE_SIZE - off, len - done);
        int ret = g_access_process_vm(task, va + done, (void *)(src + done), (int)chunk, FOLL_WRITE | FOLL_FORCE);
        if (ret != (int)chunk) break;
        done += chunk;
    }
    put_task_struct(task); return done;
}

static u64 ask_write_phys(struct mm_struct *mm, u64 va, const u8 *src, u64 len, pid_t pid)
{
    u64 n1, n2, n3;
    n1 = ask_write_direct(mm, va, src, len); if (n1 == len) return len;
    n2 = ask_write_anon_cow(mm, va + n1, src + n1, len - n1); if (n1 + n2 == len) return len;
    n3 = ask_write_apv(mm, va + n1 + n2, src + n1 + n2, len - n1 - n2, pid);
    return n1 + n2 + n3;
}

/* 读路径 */
static long ask_read_phys(struct mm_struct *mm, u64 va, void __user *ubuf, u64 len)
{
    u64 done = 0;
    while (done < len) {
        u64 off = (va + done) & (PAGE_SIZE - 1); u64 chunk = min_t(u64, PAGE_SIZE - off, len - done);
        void *ptep = NULL; int level = 0; u64 pa; void *kva;
        rcu_read_lock(); pa = ask_walk_va(mm, va + done, &ptep, &level);
        if (!pa || !ask_still_valid(ptep, pa, level)) {
            rcu_read_unlock();
            { char tmp[PAGE_SIZE]; if (ask_swap_read(mm, va + done, tmp, chunk) != 0) return -EFAULT;
              if (copy_to_user((char __user *)ubuf + done, tmp, chunk)) return -EFAULT; done += chunk; continue; }
        }
        rcu_read_unlock();
        kva = ask_map_phys(pa & PAGE_MASK); if (!kva) return -EBUSY;
        ask_dc_inval((char *)kva + off, chunk);
        if (copy_to_user((char __user *)ubuf + done, (char *)kva + off, chunk)) { ask_map_put(kva); return -EFAULT; }
        ask_map_put(kva); done += chunk;
    }
    return 0;
}

static long ask_read_kernel(struct mm_struct *mm, u64 va, void *kbuf, u64 len)
{
    u64 done = 0;
    while (done < len) {
        u64 off = (va + done) & (PAGE_SIZE - 1); u64 chunk = min_t(u64, PAGE_SIZE - off, len - done);
        void *ptep = NULL; int level = 0; u64 pa; void *kva;
        rcu_read_lock(); pa = ask_walk_va(mm, va + done, &ptep, &level);
        if (!pa || !ask_still_valid(ptep, pa, level)) { rcu_read_unlock(); return -EFAULT; }
        rcu_read_unlock();
        kva = ask_map_phys(pa & PAGE_MASK); if (!kva) return -EBUSY;
        ask_dc_inval((char *)kva + off, chunk); memcpy((char *)kbuf + done, (char *)kva + off, chunk);
        ask_map_put(kva); done += chunk;
    }
    return 0;
}

/* 写事务 */
static long ask_txn_write(struct mm_struct *mm, pid_t pid, u64 rva, const u8 *payload, u64 len)
{
    u8 *snap; u64 n1, n2, n3, total; int need_icache;
    snap = kvmalloc(len, GFP_KERNEL); if (!snap) return -ENOMEM;
    if (ask_read_kernel(mm, rva, snap, len) != (long)len) { kvfree(snap); return -EFAULT; }
    n1 = ask_write_direct(mm, rva, payload, len);
    n2 = (n1 < len) ? ask_write_anon_cow(mm, rva + n1, payload + n1, len - n1) : 0;
    n3 = (n1 + n2 < len) ? ask_write_apv(mm, rva + n1 + n2, payload + n1 + n2, len - n1 - n2, pid) : 0;
    total = n1 + n2 + n3;
    if (total == len) {
        u8 *verify = kvmalloc(len, GFP_KERNEL);
        if (verify) {
            if (ask_read_kernel(mm, rva, verify, len) == (long)len && memcmp(verify, payload, len) == 0) {
                need_icache = 0;
                mmap_read_lock(mm);
                { struct vm_area_struct *vma = find_vma(mm, rva); if (vma && rva >= vma->vm_start && (vma->vm_flags & VM_EXEC)) need_icache = 1; }
                mmap_read_unlock(mm);
                if (need_icache) {
                    void *ptep = NULL; int level = 0; u64 pa;
                    rcu_read_lock(); pa = ask_walk_va(mm, rva, &ptep, &level); rcu_read_unlock();
                    if (pa) { void *kva = ask_map_phys(pa & PAGE_MASK); if (kva) { ask_icache_sync(kva, len); ask_map_put(kva); } }
                }
                kvfree(verify); kvfree(snap); return 0;
            }
            kvfree(verify);
        }
    }
    if (total > 0) { pr_warn("ask: txn rollback %llu/%llu\n", total, len); ask_write_phys(mm, rva, snap, total, pid); }
    kvfree(snap); return total == 0 ? -EIO : -EAGAIN;
}

/* 模块基址 5.10 (链表遍历) */
static long ask_module_base(struct mm_struct *mm, const char *name, u64 *base_out, u64 *size_out)
{
    struct vm_area_struct *vma; int found = 0; u64 base = 0, end = 0;
    mmap_read_lock(mm);
    for (vma = mm->mmap; vma; vma = vma->vm_next) {
        const char *fname = NULL;
        if (!vma->vm_file) continue;
        fname = vma->vm_file->f_path.dentry->d_name.name;
        if (!fname) continue;
        if (strstr(fname, name)) {
            if (!found) { base = vma->vm_start; end = vma->vm_end; found = 1; }
            else { if (vma->vm_start < base) base = vma->vm_start; if (vma->vm_end > end) end = vma->vm_end; }
        }
    }
    mmap_read_unlock(mm);
    if (!found) return -ENOENT;
    if (base_out) *base_out = base; if (size_out) *size_out = end - base;
    return 0;
}

/* 扫描 */
static long ask_scan_mem(struct mm_struct *mm, u64 start, u64 end, const u8 *pattern, u32 plen, u64 *hits, u32 max_hits, u32 *count_out)
{
    u8 page_buf[PAGE_SIZE]; u64 addr = start; u32 count = 0; u32 i;
    if (plen == 0 || plen > 256 || start >= end) return -EINVAL;
    while (addr < end && count < max_hits) {
        u64 chunk; u64 page_off = addr & (PAGE_SIZE - 1);
        chunk = min_t(u64, PAGE_SIZE - page_off, end - addr);
        {
            u64 page_va = addr & PAGE_MASK; void *ptep = NULL; int level = 0; u64 pa;
            rcu_read_lock(); pa = ask_walk_va(mm, page_va, &ptep, &level); rcu_read_unlock();
            if (!pa || !ask_still_valid(ptep, pa, level)) { addr += chunk; continue; }
            { void *kva = ask_map_phys(pa & PAGE_MASK); if (!kva) { addr += chunk; continue; }
              ask_dc_inval(kva, PAGE_SIZE); memcpy(page_buf, kva, PAGE_SIZE); ask_map_put(kva); }
        }
        {
            u32 search_end = (page_off + chunk >= PAGE_SIZE) ? PAGE_SIZE - plen + 1 : (page_off + chunk - plen + 1);
            u32 start_idx = page_off;
            if (page_off + plen <= PAGE_SIZE) {
                for (i = start_idx; i < search_end && count < max_hits; i++)
                    if (memcmp(page_buf + i, pattern, plen) == 0) hits[count++] = (addr & PAGE_MASK) + i;
            }
        }
        addr += chunk;
    }
    *count_out = count; return 0;
}

/* 物理直读 */
static long ask_phys_read(u64 pa, void __user *ubuf, u64 len)
{
    u64 done = 0;
    while (done < len) {
        u64 off = (pa + done) & (PAGE_SIZE - 1); u64 chunk = min_t(u64, PAGE_SIZE - off, len - done);
        u64 page_pa = (pa + done) & PAGE_MASK; void *kva;
        if (!ask_pfn_ok(page_pa)) return -EFAULT;
        kva = ask_map_phys(page_pa); if (!kva) return -EBUSY;
        ask_dc_inval((char *)kva + off, chunk);
        if (copy_to_user((char __user *)ubuf + done, (char *)kva + off, chunk)) { ask_map_put(kva); return -EFAULT; }
        ask_map_put(kva); done += chunk;
    }
    return 0;
}

/* 自校准 */
static int ask_selfcheck(void)
{
    struct mm_struct *mm = current->mm;
    unsigned long va = (unsigned long)&ask_selfcheck;
    void *ptep = NULL; int level = 0; u64 pa, back_va; struct page *page;
    if (!mm) { pr_warn("ask: 自校准跳过（无 current->mm）\n"); return 0; }
    pa = ask_walk_va(mm, va, &ptep, &level);
    if (!pa) { pr_err("ask: 自校准失败 —— 走查不出 PA\n"); return -EINVAL; }
    back_va = ask_phys_to_virt(pa & PAGE_MASK) | (va & (PAGE_SIZE - 1));
    if (*(unsigned char *)back_va != *(unsigned char *)va) {
        pr_err("ask: 自校准失败 —— phys_to_virt 回环不一致\n"); return -EINVAL;
    }
    page = pfn_to_page(pa >> PAGE_SHIFT);
    if (!page) { pr_err("ask: 自校准失败 —— pfn_to_page=NULL\n"); return -EINVAL; }
    if (PageAnon(page)) { pr_err("ask: 自校准失败 —— 代码页被判匿名\n"); return -EINVAL; }
    if (!mmap_read_trylock(mm)) pr_warn("ask: 自校准注意 —— mmap_lock 有竞争\n"); else mmap_read_unlock(mm);
    pr_info("ask: 自校准通过 (va=%lx pa=%llx level=%d)\n", va, pa, level);
    return 0;
}

/* ioctl 分发 */
static long ask_ioctl(struct file *f, unsigned int cmd, unsigned long arg)
{
    void __user *uarg = (void __user *)arg;
    if (_IOC_TYPE(cmd) != ASK_IOC_MAGIC) return -ENOTTY;

    switch (cmd) {
    case ASK_IOC_ATTACH: {
        struct ask_req r; if (copy_from_user(&r, uarg, sizeof(r))) return -EFAULT;
        ask_audit_log(r.slot, 4, 0, 0, 0); return ask_attach_slot(r.slot, (pid_t)r.pid);
    }
    case ASK_IOC_DETACH: {
        struct ask_req r; if (copy_from_user(&r, uarg, sizeof(r))) return -EFAULT;
        ask_detach_slot(r.slot); return 0;
    }
    case ASK_IOC_RW: {
        struct ask_req r; struct mm_struct *mm; long ret;
        if (copy_from_user(&r, uarg, sizeof(r))) return -EFAULT;
        if (!r.size || r.size > (8UL<<20)) return -EINVAL;
        if (r.remote_va == 0 || r.remote_va >= (1UL<<47)) return -EINVAL;
        if (!ASK_ACCESS_OK((void __user *)r.local_va, r.size)) return -EFAULT;
        mm = ask_get_mm_slot(r.slot, NULL); if (!mm) return -ESRCH;
        if (r.flags & ASK_F_TTBR) {
            u64 ttbr0; char *tmp = kmalloc(r.size, GFP_KERNEL);
            if (!tmp) { mmput(mm); return -ENOMEM; }
            ask_get_mm_slot(r.slot, &ttbr0);
            if (r.flags & ASK_F_WRITE) {
                if (copy_from_user(tmp, (void __user *)r.local_va, r.size)) { kfree(tmp); mmput(mm); return -EFAULT; }
                ret = ask_ttbr_write(r.remote_va, tmp, r.size, ttbr0) ? -EFAULT : 0;
            } else {
                if (ask_ttbr_read(tmp, r.remote_va, r.size, ttbr0)) { kfree(tmp); mmput(mm); return -EFAULT; }
                ret = copy_to_user((void __user *)r.local_va, tmp, r.size) ? -EFAULT : 0;
            }
            kfree(tmp);
        } else if (r.flags & ASK_F_WRITE) {
            char *tmp = kmalloc(r.size, GFP_KERNEL); if (!tmp) { mmput(mm); return -ENOMEM; }
            if (copy_from_user(tmp, (void __user *)r.local_va, r.size)) { kfree(tmp); mmput(mm); return -EFAULT; }
            ret = ask_txn_write(mm, ask_get_pid_slot(r.slot), r.remote_va, tmp, r.size); kfree(tmp);
        } else if (r.flags & ASK_F_LINEAR) {
            ret = ask_read_phys(mm, r.remote_va, (void __user *)r.local_va, r.size);
        } else {
            ret = ask_read_phys(mm, r.remote_va, (void __user *)r.local_va, r.size);
        }
        ask_audit_log(r.slot, (r.flags & ASK_F_WRITE) ? 2 : 1, r.remote_va, r.size, (s32)ret);
        mmput(mm); return ret;
    }
    case ASK_IOC_STATUS: {
        struct ask_status st; int i;
        memset(&st, 0, sizeof(st));
        for (i = 0; i < ASK_MAX_TARGETS; i++) {
            st.attached[i] = g_tgts[i].used; st.pids[i] = g_tgts[i].pid;
            st.pgds[i] = g_tgts[i].mm ? (u64)g_tgts[i].mm->pgd : 0; st.ttbr0s[i] = g_tgts[i].ttbr0;
        }
        st.map_total = ASK_SLOT_NR; st.map_used = 0;
        for (i = 0; i < ASK_SLOT_NR; i++) if (g_slot[i].pa) st.map_used++;
        st.audit_head = g_audit_head;
        return copy_to_user(uarg, &st, sizeof(st)) ? -EFAULT : 0;
    }
    case ASK_IOC_BATCH: {
        struct ask_batch_req req; struct mm_struct *mm; u32 i;
        if (copy_from_user(&req, uarg, sizeof(req))) return -EFAULT;
        if (req.count == 0 || req.count > ASK_BATCH_MAX) return -EINVAL;
        mm = ask_get_mm_slot(req.slot, NULL); if (!mm) return -ESRCH;
        for (i = 0; i < req.count; i++) {
            struct ask_iov *iv = &req.iov[i]; long ret;
            if (!iv->size || iv->size > (1UL<<20) || !iv->remote_va) { iv->ret = -EINVAL; continue; }
            if (!ASK_ACCESS_OK((void __user *)iv->local_va, iv->size)) { iv->ret = -EFAULT; continue; }
            if (req.flags & ASK_F_WRITE) {
                char *tmp = kmalloc(iv->size, GFP_KERNEL); if (!tmp) { iv->ret = -ENOMEM; continue; }
                if (copy_from_user(tmp, (void __user *)iv->local_va, iv->size)) { kfree(tmp); iv->ret = -EFAULT; continue; }
                ret = ask_txn_write(mm, ask_get_pid_slot(req.slot), iv->remote_va, tmp, iv->size); kfree(tmp);
            } else {
                ret = ask_read_phys(mm, iv->remote_va, (void __user *)iv->local_va, iv->size);
            }
            iv->ret = (s32)ret;
        }
        mmput(mm); return copy_to_user(uarg, &req, sizeof(req)) ? -EFAULT : 0;
    }
    case ASK_IOC_SCAN: {
        struct ask_scan_req req; struct mm_struct *mm; u8 pat[256]; u64 *hits; u32 count = 0; long ret;
        if (copy_from_user(&req, uarg, sizeof(req))) return -EFAULT;
        if (req.pattern_len == 0 || req.pattern_len > 256 || req.max_hits == 0 || req.max_hits > ASK_SCAN_MAX_HITS) return -EINVAL;
        if (copy_from_user(pat, (void __user *)req.pattern_va, req.pattern_len)) return -EFAULT;
        hits = kvmalloc(req.max_hits * sizeof(u64), GFP_KERNEL); if (!hits) return -ENOMEM;
        mm = ask_get_mm_slot(req.slot, NULL); if (!mm) { kvfree(hits); return -ESRCH; }
        ret = ask_scan_mem(mm, req.start, req.end, pat, req.pattern_len, hits, req.max_hits, &count);
        mmput(mm); req.hit_count = count;
        if (ret == 0 && count > 0) copy_to_user((void __user *)req.hits_va, hits, count * sizeof(u64));
        kvfree(hits); return copy_to_user(uarg, &req, sizeof(req)) ? -EFAULT : 0;
    }
    case ASK_IOC_MODULE: {
        struct ask_mod_req req; struct mm_struct *mm; long ret;
        if (copy_from_user(&req, uarg, sizeof(req))) return -EFAULT;
        if (req.name[ASK_MODNAME_MAX-1] != 0) return -EINVAL;
        mm = ask_get_mm_slot(req.slot, NULL); if (!mm) return -ESRCH;
        ret = ask_module_base(mm, req.name, &req.base_out, &req.size_out); mmput(mm);
        return copy_to_user(uarg, &req, sizeof(req)) ? -EFAULT : 0;
    }
    case ASK_IOC_PHYS_READ: {
        struct ask_phys_req req;
        if (copy_from_user(&req, uarg, sizeof(req))) return -EFAULT;
        if (!req.size || req.size > (1UL<<20) || !ASK_ACCESS_OK((void __user *)req.local_va, req.size)) return -EINVAL;
        return ask_phys_read(req.pa, (void __user *)req.local_va, req.size);
    }
    case ASK_IOC_AUDIT: {
        struct ask_audit_ent ents[64]; unsigned long flags; u32 i, head;
        spin_lock_irqsave(&g_audit_lock, flags); head = g_audit_head; spin_unlock_irqrestore(&g_audit_lock, flags);
        for (i = 0; i < 64; i++) {
            u32 idx = (head - 64 + i) & 63;
            ents[i].ts_ns = g_audit[idx].ts_ns; ents[i].slot = g_audit[idx].slot;
            ents[i].op = g_audit[idx].op; ents[i].remote_va = g_audit[idx].remote_va;
            ents[i].size = g_audit[idx].size; ents[i].ret = g_audit[idx].ret; ents[i]._pad = 0;
        }
        return copy_to_user(uarg, ents, sizeof(ents)) ? -EFAULT : 0;
    }
    default: return -ENOTTY;
    }
}

static const struct file_operations ask_fops = {
    .owner = THIS_MODULE, .unlocked_ioctl = ask_ioctl, .compat_ioctl = ask_ioctl,
};
static struct miscdevice ask_misc = {
    .minor = MISC_DYNAMIC_MINOR, .name = "askrw", .fops = &ask_fops, .mode = 0666,
};

static int __init ask_init(void)
{
    int ret;
    ask_cache_line_init();
    pr_info("ask: cache line=%u, kernel=%s\n", g_cache_line, UTS_RELEASE);
    ret = ask_resolve_syms(); if (ret) return ret;
    ret = ask_selfcheck(); if (ret) return ret;
    ret = ask_pool_init(); if (ret) return ret;
    ret = misc_register(&ask_misc); if (ret) { ask_pool_exit(); return ret; }
    pr_info("ask: ready, /dev/askrw (magic 'A')\n");
    return 0;
}

static void __exit ask_exit(void)
{
    int i;
    misc_deregister(&ask_misc);
    for (i = 0; i < ASK_MAX_TARGETS; i++) ask_detach_slot(i);
    ask_pool_exit();
    pr_info("ask: bye\n");
}

module_init(ask_init);
module_exit(ask_exit);
