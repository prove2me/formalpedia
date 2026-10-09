-- Prove2me | Theorems.Thm_NonconvexSaddle_PGDVar_lemma_19
-- name    : NonconvexSaddle.PGDVar.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:10:49.97398+00:00
-- url     : https://prove2.me/theorems/84852c16-b58d-43fa-b4b3-ef74ea463064
-- title:
--   Lemma 19 — descent lemma: a gradient step with η ≤ 1/ℓ decreases f by η‖∇f‖²/2
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ satisfy Assumption A with constants $\ell,\rho>0$, and let the step size satisfy $0<\eta\le 1/\ell$. Then for every $x\in\mathbb R^d$ the gradient descent step $x^+=x-\eta\nabla f(x)$ satisfies
--   $$f(x^+)-f(x)\le-\frac{\eta}{2}\|\nabla f(x)\|^2 .$$
--
--   Applied along a gradient descent sequence $\{x_t\}$ this is $f(x_{t+1})-f(x_t)\le-\eta\|\nabla f(x_t)\|^2/2$: the function value decreases at every step, by a definite amount whenever the gradient is large. It is used in the proof of Theorem 18 to bound the number of large-gradient iterations, and in Lemma 21.
--
--   **Formalization Note** $\eta>0$ is the paper's standing convention for step sizes (p. 6, after Eq. (1)); for $\eta<0$ the inequality is false. Only the gradient Lipschitz half of Assumption A matters, but the hypothesis is stated as on the page.
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, p. 13, Lemma 19

import Mathlib
import Definitions.Def_NonconvexSaddle_PGDVar_Setting

open scoped RealInnerProductSpace

namespace NonconvexSaddle.PGDVar

/-- Lemma 19 (Descent Lemma), arXiv:1902.04811v2, p. 13: if `f` satisfies Assumption A and the step
size satisfies `0 < η ≤ 1/ℓ` (`η > 0` is the standing convention of Eq. (1), p. 6), then one gradient
descent step decreases `f` by at least `η‖∇f(x)‖²/2`. -/
theorem lemma_19 {d : ℕ} (f : NonconvexSaddle.PSGD.E d → ℝ) (ℓ ρ η : ℝ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (hA : NonconvexSaddle.PSGD.AssumptionA f ℓ ρ) (hη : 0 < η) (hηℓ : η ≤ 1 / ℓ) (x : NonconvexSaddle.PSGD.E d) :
    f (gdStep f η x) - f x ≤ -η * ‖gradient f x‖ ^ 2 / 2 := by sorry

end NonconvexSaddle.PGDVar
