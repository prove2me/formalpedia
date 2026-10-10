-- Prove2me | Theorems.Thm_NAGFlow_GradCorr_eq_94
-- name    : NAGFlow.GradCorr.eq_94
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:36.724694+00:00
-- url     : https://prove2.me/theorems/e6cb0c22-3758-4c3f-88ce-61b7627b35c7
-- title:
--   (94), p. 22 — for f ∈ S^{1,1}_{μ,L}, one gradient step with step 1/L decreases f by at least ‖∇f(y)‖²/(2L)
-- statement:
--   Let $V$ be a real Hilbert space and $f\in\mathcal S^{1,1}_{\mu,L}$ with $0\le\mu\le L<\infty$. For $y\in V$, let $x'=y-\frac1L\nabla f(y)$. Then
--   $$f(x')-f(y)\le-\frac{1}{2L}\|\nabla f(y)\|^2.\qquad(94)$$
--
--   This is the basic gradient descent inequality, which the paper derives from (4). In the corrected scheme (91), with $y=y_k$ and $x'=x_{k+1}$, it is the decay property that cancels the gradient-norm term of (93).
--
--   **Formalization Note.** $\|\cdot\|_*$ is the norm of $V$ (Riesz). The quadratic upper bound (4) is not assumed; it follows from the Lipschitz continuity (3) of the gradient, which is part of the class.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, Eq. (94), p. 22; (4) p. 2

import Mathlib
import Definitions.Def_NAGFlow_GradCorr_Setting

namespace NAGFlow.GradCorr

/-- The gradient descent inequality (94) (Luo & Chen, arXiv:1909.03145v4, p. 22). Let
`f ∈ S^{1,1}_{μ,L}` with `0 ≤ μ ≤ L < ∞`. If `x' = y − (1/L)∇f(y)` (the correction step of (91)),
then `f(x') − f(y) ≤ −(1/(2L))‖∇f(y)‖²`. -/
theorem eq_94 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ L : ℝ) (hf : NAGFlow.PredCorr.IsS11 f gradf μ L)
    (y x' : V) (hx' : x' - y = -(1 / L) • gradf y) :
    f x' - f y ≤ -(1 / (2 * L)) * ‖gradf y‖ ^ 2 := by sorry

end NAGFlow.GradCorr
