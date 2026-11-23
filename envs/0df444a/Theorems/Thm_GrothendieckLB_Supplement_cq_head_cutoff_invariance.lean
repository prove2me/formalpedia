-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_head_cutoff_invariance
-- name    : GrothendieckLB.Supplement.cq_head_cutoff_invariance
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T19:39:35.233953+00:00
-- url     : https://prove2.me/theorems/fae07324-f481-4380-afc5-e13bde6ddd51
-- title:
--   Cutoff invariance of the cubic–quintic coefficient certificate
-- statement:
--   The fixed-point certificate for the cubic–quintic rounding scheme gives the same answer at any two cutoffs $n\le N$ when each requested degree $2j+3$ is at most $n$. The equality includes the effects of outward rounding. It permits certificates computed on smaller moment and Hermite tables to be used in the full degree-251 calculation.
-- source:
--   Restriction of the integer Hermite recurrence in the cubic–quintic certificate, Prove2Me theorem 7286b935-9e05-49d4-81b5-23facaf49129.

import Definitions.Def_GrothendieckLB_Supplement_cqNonlinearHeadCheck

namespace GrothendieckLB.Supplement

theorem cq_head_cutoff_invariance {n N : ℕ} (hn : n ≤ N) (indices : List ℕ)
    (h : ∀ j ∈ indices, 2*j+3 ≤ n) :
    CQHeadArithmetic.verifyList n indices = CQHeadArithmetic.verifyList N indices := by sorry

end GrothendieckLB.Supplement
