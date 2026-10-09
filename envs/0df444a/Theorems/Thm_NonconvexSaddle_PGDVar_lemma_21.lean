-- Prove2me | Theorems.Thm_NonconvexSaddle_PGDVar_lemma_21
-- name    : NonconvexSaddle.PGDVar.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:10:58.605522+00:00
-- url     : https://prove2.me/theorems/5ad1591e-d0da-47a8-8e23-51dc9222fff1
-- title:
--   Lemma 21 — improve or localize: ‖x_τ − x₀‖ ≤ √(2ηt(f(x₀) − f(x_t))) for t ≥ τ > 0
-- statement:
--   Let $f$ satisfy Assumption A with $\ell,\rho>0$, let $0<\eta\le1/\ell$, and let $x_0\in\mathbb R^d$. Let $\{x_t\}$ be the gradient descent sequence $x_{t+1}=x_t-\eta\nabla f(x_t)$. Then for all integers $t\ge\tau>0$,
--   $$\|x_\tau-x_0\|\le\sqrt{2\eta t\,\bigl(f(x_0)-f(x_t)\bigr)} .$$
--
--   If gradient descent does not decrease the function value much over $t$ iterations, then all iterates up to time $t$ stay in a small neighbourhood of the starting point. This localization is the main simplification of the §5 analysis and is used in the proof of Lemma 22.
--
--   **Formalization Note** $x_\tau$ is the $\tau$-fold iterate of the map $x\mapsto x-\eta\nabla f(x)$ applied to $x_0$; $\tau$ and $t$ are natural numbers. "Under the setting of Lemma 19" means Assumption A and $0<\eta\le1/\ell$.
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, p. 13, Lemma 21

import Mathlib
import Definitions.Def_NonconvexSaddle_PGDVar_Setting

open scoped RealInnerProductSpace

namespace NonconvexSaddle.PGDVar

/-- Lemma 21 (Improve or Localize), arXiv:1902.04811v2, p. 13: under the setting of Lemma 19
(Assumption A, `0 < η ≤ 1/ℓ`), the gradient descent sequence `x_τ = (x ↦ x − η∇f(x))^τ (x₀)` satisfies
`‖x_τ − x₀‖ ≤ √(2ηt(f(x₀) − f(x_t)))` for all `t ≥ τ > 0`. -/
theorem lemma_21 {d : ℕ} (f : NonconvexSaddle.PSGD.E d → ℝ) (ℓ ρ η : ℝ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (hA : NonconvexSaddle.PSGD.AssumptionA f ℓ ρ) (hη : 0 < η) (hηℓ : η ≤ 1 / ℓ) (x₀ : NonconvexSaddle.PSGD.E d) (τ t : ℕ)
    (hτ : 0 < τ) (hτt : τ ≤ t) :
    ‖(gdStep f η)^[τ] x₀ - x₀‖ ≤
      Real.sqrt (2 * η * t * (f x₀ - f ((gdStep f η)^[t] x₀))) := by sorry

end NonconvexSaddle.PGDVar
