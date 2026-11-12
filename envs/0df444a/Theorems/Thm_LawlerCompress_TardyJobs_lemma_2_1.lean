-- Prove2me | Theorems.Thm_LawlerCompress_TardyJobs_lemma_2_1
-- name    : LawlerCompress.TardyJobs.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:25:35.601514+00:00
-- url     : https://prove2.me/theorems/76468596-1e20-44c0-aef2-87909e7d5422
-- title:
--   Lemma 2.1 — Canonical completion times form an interval
-- statement:
--   Let I be an EDD instance on m≥1 machines with n≥1 jobs. For every input job j, the canonical endpoint a_j satisfies
--
--   $$p_j\le a_j\le d_j+1,\qquad\bar C_j=\{a_j,a_j+1,\ldots,d_j\},\qquad\bar C_j=\varnothing\Longrightarrow a_j=d_j+1.$$
--
--   Here priority is weight followed by larger index, and a_j is computed as the least canonical time with the stated empty-set default. This identifies the interval that the later algorithm enumerates.
--
--   **Formalization Note** The endpoint is a shared definition, not an arbitrary witness chosen separately in each theorem.
--
--   Differences from the source:
--   - encoding: jobs and machines numbered from one; positive integral data; a nonempty input with a maximum due date → Fin n jobs and Fin m machines, natural data in Instance, with m,n ≥ 1; reason: zero-based reindexing preserves every schedule and excludes only the undefined empty maximum
-- source:
--   Klaus Jansen, Björn Schumacher, Corinna Wambsganz, Compressing the Lawler-Moore Dynamic Program for Weighted Tardy Jobs, STOC 2027 submission #354 (October 2026), p. 4, Lemma 2.1

import Definitions.Def_LawlerCompress_TardyJobs_Canonical

set_option autoImplicit false

namespace LawlerCompress.TardyJobs

theorem lemma_2_1 {m : ℕ} (hm : 1 ≤ m) (I : Instance m)
    (hn : 1 ≤ I.n) (hedd : EDD I) (j : Fin I.n) :
    I.p j ≤ a I j ∧ a I j ≤ I.d j + 1 ∧
    cbar I j = Finset.Icc (a I j) (I.d j) ∧
    (cbar I j = ∅ → a I j = I.d j + 1) := by sorry

end LawlerCompress.TardyJobs
