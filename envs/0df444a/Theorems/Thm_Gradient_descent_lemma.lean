-- Prove2me | Theorems.Thm_Gradient_descent_lemma
-- name    : Gradient.descent_lemma
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:31.085822+00:00
-- url     : https://prove2.me/theorems/959ec98c-6149-47f3-b842-be8cf2a44b71
-- title:
--   The descent lemma for an `L`-Lipschitz gradient
-- statement:
--   **The descent lemma.** Let $H$ be a real inner product space and let
--   $F : H \to \mathbb{R}$ be differentiable with gradient $\nabla F$, and suppose $\nabla F$ is
--   $L$-Lipschitz:
--
--   $$
--   \|\nabla F(x) - \nabla F(y)\| \;\le\; L\,\|x - y\| \qquad \text{for all } x, y \in H .
--   $$
--
--   Then $F$ is bounded above by its own linearization plus a quadratic term: for all $x, y \in H$,
--
--   $$
--   F(y) \;\le\; F(x) \;+\; \langle \nabla F(x),\, y - x \rangle \;+\; \frac{L}{2}\,\|y - x\|^{2}.
--   $$
--
--   No convexity is required. This quadratic upper bound is the single most used inequality in the
--   analysis of first-order methods: substituting a gradient step $y = x - \tfrac1L \nabla F(x)$
--   turns it into the per-iteration decrease $F(y) \le F(x) - \tfrac{1}{2L}\|\nabla F(x)\|^2$, from
--   which the convergence rates of gradient descent and its proximal and stochastic variants
--   follow.
-- source:
--   Y. Nesterov, Lectures on Convex Optimization, 2nd ed., Springer 2018, Lemma 1.2.3 (the descent lemma); carved from the accepted proof of RelaxedPRS.Linear.theorem_4_3, https://prove2.me/submissions/23766413-5769-4c79-8267-9febba86ff5e

import Mathlib

set_option autoImplicit false
open scoped InnerProductSpace
open scoped RealInnerProductSpace

theorem Gradient.descent_lemma {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} {L : ℝ} (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x y : E) :
    F y ≤ F x + ⟪G x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by sorry
