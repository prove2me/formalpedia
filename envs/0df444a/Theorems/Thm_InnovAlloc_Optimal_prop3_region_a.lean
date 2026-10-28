-- Prove2me | Theorems.Thm_InnovAlloc_Optimal_prop3_region_a
-- name    : InnovAlloc.Optimal.prop3_region_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:25.507047+00:00
-- url     : https://prove2.me/theorems/fd91e314-7a9d-4020-aa24-5c69130687bd
-- title:
--   Proof of Proposition 3, p. 39 — one-agent profit dominates below the α threshold
-- statement:
--   Under $\alpha\in[0,1]$, $\gamma\in(0,1)$, and $\gamma B>2$, suppose $\alpha<6\sqrt2-8$. Then the principal's equal-split profit is strictly lower than its one-agent profit:
--
--   $$\Pi_d(B)<\Pi_m(B).$$
--
--   This is the region-a comparison used to identify the one-agent allocation in Theorem 1. The comparison uses the two closed-form profits in equations (8) and (11).
-- source:
--   Gao, Fan, Huang & Chen, “Resource Allocation Among Competing Innovators”, SSRN preprint 3658157 (February 2021), p. 39, proof of Proposition 3, paragraph beginning ‘When α < 6√2 − 8’

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Model

namespace InnovAlloc.Optimal

/-- Proof of Proposition 3, p. 39: below the critical competition parameter,
    the monopoly profit is strictly larger when `γB > 2`. -/
theorem prop3_region_a (α γ B : ℝ) (hs : Standing α γ)
    (ha : α < alphaLow) (hB : 2 < γ * B) :
    profitDuo α γ B < profitMono γ B := by sorry

end InnovAlloc.Optimal
