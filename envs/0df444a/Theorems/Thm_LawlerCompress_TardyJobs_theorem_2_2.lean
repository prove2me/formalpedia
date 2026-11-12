-- Prove2me | Theorems.Thm_LawlerCompress_TardyJobs_theorem_2_2
-- name    : LawlerCompress.TardyJobs.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:25:14.371099+00:00
-- url     : https://prove2.me/theorems/36d6082f-20f8-4f6e-8f01-cfb0bf84b1bf
-- title:
--   Theorem 2.2 — An optimal canonical schedule with EDD prefixes
-- statement:
--   For any nonempty EDD instance I on m≥1 machines, there exists one optimal schedule τ such that
--
--   $$\forall j,\quad C_j(\tau)\le d_j\Longrightarrow C_j(\tau)\in\bar C_j.$$
--
--   On every machine, the on-time jobs form a prefix strictly increasing in the input job indices, followed by the late jobs. Both properties hold for the same optimal schedule. This provides the full scheduling target used by the compressed dynamic program.
--
--   **Formalization Note** Strict index order preserves the source convention even when due dates tie; every job, including every late job, appears once.
--
--   Differences from the source:
--   - encoding: jobs and machines numbered from one; positive integral data; a nonempty input with a maximum due date → Fin n jobs and Fin m machines, natural data in Instance, with m,n ≥ 1; reason: zero-based reindexing preserves every schedule and excludes only the undefined empty maximum
-- source:
--   Klaus Jansen, Björn Schumacher, Corinna Wambsganz, Compressing the Lawler-Moore Dynamic Program for Weighted Tardy Jobs, STOC 2027 submission #354 (October 2026), p. 4, Theorem 2.2

import Definitions.Def_LawlerCompress_TardyJobs_Canonical

set_option autoImplicit false

namespace LawlerCompress.TardyJobs

theorem theorem_2_2 {m : ℕ} (hm : 1 ≤ m) (I : Instance m)
    (hn : 1 ≤ I.n) (hedd : EDD I) :
    ∃ τ : JobLists I, IsOptSchedule I τ ∧
      (∀ j, completion I τ j ≤ I.d j → completion I τ j ∈ cbar I j) ∧
      OnTimeEDDPrefix I τ := by sorry

end LawlerCompress.TardyJobs
