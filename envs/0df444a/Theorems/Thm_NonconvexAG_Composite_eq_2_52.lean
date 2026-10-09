-- Prove2me | Theorems.Thm_NonconvexAG_Composite_eq_2_52
-- name    : NonconvexAG.Composite.eq_2_52
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:35:23.226382+00:00
-- url     : https://prove2.me/theorems/95b846c8-3caf-487b-912b-8f5e5adacf0a
-- title:
--   (2.52) — ‖x^md_k − x*‖² + α_k(1−α_k)‖x^ag_{k−1} − x_{k−1}‖² ≤ 2(‖x*‖² + 2M²)
-- statement:
--   Run Algorithm 2 with any gradient map, step sizes $\alpha_1=1$, $\alpha_k\in(0,1)$ ($k\ge2$), $\beta_k,\lambda_k>0$, and a map $\mathcal P$ satisfying Assumption 2 with constant $M$, from a starting point with $\|x_0\|\le M$. Then for every $k\ge1$ and every point $x^*\in\mathbb R^n$,
--   $$\|x^{md}_k-x^*\|^2+\alpha_k(1-\alpha_k)\|x^{ag}_{k-1}-x_{k-1}\|^2\le2\big(\|x^*\|^2+2M^2\big).$$
--
--   It bounds the nonconvexity terms of the summed inequality uniformly in $k$, which is where Assumption 2 enters the proof of Theorem 2.
--
--   **Formalization Note** Only the outer ends of the printed chain are stated. The bound holds for every point $x^*$; the paper applies it at an optimal solution. **Added hypothesis** $\|x_0\|\le M$: at $k=1$ the chain uses $\|x_0\|=\|x^{ag}_0\|\le M$, but $x_0$ is the input, not an output of $\mathcal P$, so Assumption 2 does not give it. It holds whenever $x_0\in\operatorname{dom}\mathcal X$ and the domain lies in the ball of radius $M$.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 13, (2.52)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Composite_ProxMap
import Definitions.Def_NonconvexAG_Composite_AGRun

namespace NonconvexAG.Composite

open ConvexOptAlg.SmoothGD

/-- (2.52), p. 13 (outer ends of the chain): under Assumption 2 and `‖x₀‖ ≤ M`, for every
`k ≥ 1` and every point `x*` (the paper applies it at an optimal solution). -/
theorem eq_2_52 {n : ℕ} (gΨ : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n) (P : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n → ℝ → NonconvexAG.Smooth.E n) (M : ℝ)
    (hA2 : Assumption2 P M) (α β lam : ℕ → ℝ) (hstep : NonconvexAG.Smooth.AGStepsizes α β lam) (x0 : NonconvexAG.Smooth.E n)
    (hx0 : ‖x0‖ ≤ M) :
    let xk : ℕ → NonconvexAG.Smooth.E n := xSeq gΨ P α β lam x0
    let xag : ℕ → NonconvexAG.Smooth.E n := xagSeq gΨ P α β lam x0
    let xmd : ℕ → NonconvexAG.Smooth.E n := xmdSeq gΨ P α β lam x0
    ∀ k, 1 ≤ k → ∀ xstar : NonconvexAG.Smooth.E n,
      ‖xmd k - xstar‖ ^ 2 + α k * (1 - α k) * ‖xag (k - 1) - xk (k - 1)‖ ^ 2 ≤
        2 * (‖xstar‖ ^ 2 + 2 * M ^ 2) := by sorry
end NonconvexAG.Composite
