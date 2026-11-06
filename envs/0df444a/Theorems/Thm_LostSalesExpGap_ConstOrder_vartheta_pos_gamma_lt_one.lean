-- Prove2me | Theorems.Thm_LostSalesExpGap_ConstOrder_vartheta_pos_gamma_lt_one
-- name    : LostSalesExpGap.ConstOrder.vartheta_pos_gamma_lt_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T22:11:37.474989+00:00
-- url     : https://prove2.me/theorems/109eaef5-5d47-4de9-ab2c-34ad71dcc50d
-- title:
--   Sec. 2.3, p. 7 — ϑ > 0 and γ ∈ [0, 1)
-- statement:
--   In the lost-sales model with strictly positive demand variance, let $r_\infty$ be the best constant order, $\phi(\theta)=e^{\theta r_\infty}\mathbb E[e^{-\theta D}]$ for $\theta\ge0$, $\gamma=\inf_{\theta\ge0}\phi(\theta)$, and $\vartheta$ the supremum of the minimizers of $\phi$ on $[0,\infty)$ ($\vartheta=\infty$ if the infimum is not attained). Then
--   $$
--   0\le\gamma<1\qquad\text{and}\qquad\vartheta>0 .
--   $$
--
--   These are what make $\gamma^{L+1}$ an exponentially decaying factor and $(1-\gamma)^{-1}$, $(e\vartheta(L+1))^{-1}$ finite in Theorem 1.
--
--   **Formalization Note** $\vartheta>0$ is stated for the case where the set of minimizers is nonempty and bounded (then $\vartheta$ is its supremum); in the other cases $\vartheta=\infty>0$ by definition.
-- source:
--   Xin, Goldberg, Optimality gap of constant-order policies decays exponentially in the lead time for lost sales models, arXiv:1409.1499v2, Sec. 2.3, p. 7

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LostSalesExpGap.ConstOrder

/-- Sec. 2.3, p. 7: `ϑ > 0` and `γ ∈ [0, 1)`. When the minimizers of `φ` on `[0, ∞)` form a
nonempty bounded set, their supremum `ϑ` is positive; otherwise `ϑ = ∞`. -/
theorem vartheta_pos_gamma_lt_one (P : CappedBaseStock.DemandLaw)
    (c : CappedBaseStock.Parameters)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P) :
    0 ≤ gamma P c ∧ gamma P c < 1 ∧
      ((phiMinimizers P c).Nonempty → BddAbove (phiMinimizers P c) →
        0 < sSup (phiMinimizers P c)) := by sorry

end LostSalesExpGap.ConstOrder
