-- Prove2me | Theorems.Thm_InnovAlloc_Optimal_prop3_region_b
-- name    : InnovAlloc.Optimal.prop3_region_b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:30.351984+00:00
-- url     : https://prove2.me/theorems/42949081-a83f-45d8-a301-cc80bdefc171
-- title:
--   Proof of Proposition 3, p. 39 — exact diversification band
-- statement:
--   Suppose $\gamma\in(0,1)$, $6\sqrt2-8\le\alpha<1/2$, and $\gamma B>2$. The principal's equal-split profit is at least its one-agent profit if and only if the effective resource level lies in the closed band
--
--   $$\Pi_m(B)\le\Pi_d(B)\quad\Longleftrightarrow\quad\gamma B\in\left[\frac{1-\alpha-\sqrt{\alpha^2+16\alpha-8}}{1-2\alpha},\frac{1-\alpha+\sqrt{\alpha^2+16\alpha-8}}{1-2\alpha}\right].$$
--
--   This comparison supplies both boundary values and their inclusive tie cases for Theorem 1's middle region.
-- source:
--   Gao, Fan, Huang & Chen, “Resource Allocation Among Competing Innovators”, SSRN preprint 3658157 (February 2021), p. 39, proof of Proposition 3, paragraph beginning ‘When 6√2 − 8 ≤ α < 1/2’

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Model

namespace InnovAlloc.Optimal

/-- Proof of Proposition 3, p. 39: the exact resource band where diversification
    weakly beats a monopoly in the middle parameter regime. -/
theorem prop3_region_b (α γ B : ℝ) (hs : Standing α γ)
    (ha0 : alphaLow ≤ α) (ha1 : α < 1 / 2) (hB : 2 < γ * B) :
    (profitMono γ B ≤ profitDuo α γ B ↔
      γ * B ∈ Set.Icc (bandLow α) (bandHigh α)) := by sorry

end InnovAlloc.Optimal
