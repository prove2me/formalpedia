-- Prove2me | Theorems.Thm_LawlerCompress_TardyJobs_lemma_3_3
-- name    : LawlerCompress.TardyJobs.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:26:33.398233+00:00
-- url     : https://prove2.me/theorems/bb8d93ee-8e4d-40e3-a28b-e70b07182cee
-- title:
--   Lemma 3.3 — Algorithm 2 upper bounds the optimal on-time weight
-- statement:
--   Let I be a nonempty EDD instance on m≥1 machines, and let w be the maximum of Algorithm 2’s final table. For every complete schedule τ,
--
--   $$\sum_j w_j\le w+L_I(\tau).$$
--
--   Equivalently, the total input weight minus w is at most the optimal late weight. The statement concerns the independent deferred-update recurrence and retains every possible schedule in the comparison. It is the optimal-value lower-bound direction needed for the main theorem.
--
--   **Formalization Note** The finite maximum is a natural number with a structural non-bottom certificate in the definition layer.
--
--   Differences from the source:
--   - encoding: jobs and machines numbered from one; positive integral data; a nonempty input with a maximum due date → Fin n jobs and Fin m machines, natural data in Instance, with m,n ≥ 1; reason: zero-based reindexing preserves every schedule and excludes only the undefined empty maximum
--   - encoding: Σ_j w_j − w ≤ OPT(I) → Σ_j w_j ≤ algValue I + lateWeight I τ for every schedule τ; reason: equivalent minimum comparison without truncated natural subtraction or an unattained infimum
-- source:
--   Klaus Jansen, Björn Schumacher, Corinna Wambsganz, Compressing the Lawler-Moore Dynamic Program for Weighted Tardy Jobs, STOC 2027 submission #354 (October 2026), p. 7, Lemma 3.3

import Definitions.Def_LawlerCompress_TardyJobs_DynamicProgram

set_option autoImplicit false

namespace LawlerCompress.TardyJobs

theorem lemma_3_3 {m : ℕ} (hm : 1 ≤ m) (I : Instance m)
    (hn : 1 ≤ I.n) (hedd : EDD I) :
    ∀ τ : JobLists I, Schedule I τ →
      totalWeight I ≤ algValue I + lateWeight I τ := by sorry

end LawlerCompress.TardyJobs
