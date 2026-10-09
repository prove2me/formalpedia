-- Prove2me | Theorems.Thm_NonconvexAG_Composite_eq_2_42
-- name    : NonconvexAG.Composite.eq_2_42
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:36:39.96134+00:00
-- url     : https://prove2.me/theorems/f8e75fa0-d256-462b-80b9-6ebe8bd35dbb
-- title:
--   (2.42) — 𝒢(x^md_k, ∇Ψ(x^md_k), β_k) = (x^md_k − x^ag_k)/β_k
-- statement:
--   Consider Algorithm 2 with any gradient map $\nabla\Psi$, any prox map $\mathcal P$, any step sizes and any starting point. For every $k\ge1$, the gradient mapping (2.38) at the middle iterate with step $\beta_k$ is the scaled difference of the middle and the aggregated iterates:
--   $$\mathcal G\big(x^{md}_k,\nabla\Psi(x^{md}_k),\beta_k\big)=\frac1{\beta_k}\big(x^{md}_k-x^{ag}_k\big).$$
--
--   This identity, immediate from (2.38) and (2.41), converts the bound on $\sum\|x^{ag}_k-x^{md}_k\|^2$ obtained in the proof of Theorem 2 into the bound (2.44) on the gradient mapping, the termination criterion of the method.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 11, (2.42)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Composite_ProxMap
import Definitions.Def_NonconvexAG_Composite_AGRun

namespace NonconvexAG.Composite

open ConvexOptAlg.SmoothGD

/-- (2.42), p. 11: along Algorithm 2, the gradient mapping at `x^md_k` with step `βₖ` is
`(x^md_k − x^ag_k)/βₖ`. -/
theorem eq_2_42 {n : ℕ} (gΨ : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n) (P : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n → ℝ → NonconvexAG.Smooth.E n) (α β lam : ℕ → ℝ) (x0 : NonconvexAG.Smooth.E n) :
    ∀ k, 1 ≤ k →
      gradMap P (xmdSeq gΨ P α β lam x0 k) (gΨ (xmdSeq gΨ P α β lam x0 k)) (β k) =
        (1 / β k) • (xmdSeq gΨ P α β lam x0 k - xagSeq gΨ P α β lam x0 k) := by sorry
end NonconvexAG.Composite
