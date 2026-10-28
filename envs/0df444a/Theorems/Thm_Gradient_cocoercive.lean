-- Prove2me | Theorems.Thm_Gradient_cocoercive
-- name    : Gradient.cocoercive
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:35.953849+00:00
-- url     : https://prove2.me/theorems/ff5b0346-a6cd-4ada-8481-f79662db4a13
-- title:
--   Cocoercivity of the gradient of a convex function with Lipschitz gradient
-- statement:
--   Let $H$ be a real inner product space and let $F : H \to \mathbb{R}$ be convex and
--   differentiable with $L$-Lipschitz gradient, $L > 0$. Then for all $x, y \in H$
--
--   $$
--   \|\nabla F(y) - \nabla F(x)\|^{2} \;\le\; 2L\,\bigl(F(y) - F(x) - \langle \nabla F(x),\, y - x\rangle\bigr).
--   $$
--
--   The quantity in brackets is the Bregman divergence of $F$ between $x$ and $y$, which is
--   nonnegative by convexity, so the inequality bounds the squared gradient displacement by the gap
--   between $F$ and its linearization.
--
--   Combined with the first-order convexity inequality this yields the usual $1/L$-cocoercivity of
--   the gradient, $\langle \nabla F(y) - \nabla F(x), y - x\rangle \ge \tfrac1L \|\nabla F(y) -
--   \nabla F(x)\|^2$, which is the property that makes the gradient step a firmly nonexpansive
--   operator and thereby drives the convergence proofs of splitting and operator-based methods.
-- source:
--   Y. Nesterov, Lectures on Convex Optimization, 2nd ed., Springer 2018, Theorem 2.1.5; carved from the accepted proof of RelaxedPRS.Linear.theorem_4_3, https://prove2.me/submissions/23766413-5769-4c79-8267-9febba86ff5e

import Mathlib

set_option autoImplicit false
open scoped InnerProductSpace
open scoped RealInnerProductSpace

theorem Gradient.cocoercive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} {L : ℝ} (hL : 0 < L)
    (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (hc : ConvexOn ℝ Set.univ F) (x y : E) :
    ‖G y - G x‖ ^ 2 ≤ 2 * L * (F y - F x - ⟪G x, y - x⟫) := by sorry
