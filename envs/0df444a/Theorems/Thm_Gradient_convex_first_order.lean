-- Prove2me | Theorems.Thm_Gradient_convex_first_order
-- name    : Gradient.convex_first_order
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:35.110958+00:00
-- url     : https://prove2.me/theorems/3d549277-310a-42e8-91ab-90b39e28021f
-- title:
--   First-order characterization of a convex differentiable function
-- statement:
--   Let $H$ be a real inner product space and let $F : H \to \mathbb{R}$ be differentiable
--   with gradient $\nabla F(x)$ at every point. If $F$ is convex, then for all $x, y \in H$
--
--   $$
--   F(x) \;+\; \langle \nabla F(x),\, y - x \rangle \;\le\; F(y).
--   $$
--
--   Geometrically: the tangent hyperplane to the graph of $F$ at any point lies below the graph.
--   This is the first-order characterization of convexity, and it is the inequality that every
--   analysis of a first-order method starts from — it is what lets a one-step bound stated in
--   terms of gradients be converted into a bound on function values.
--
--   **Formalization Note** Differentiability is stated as `HasGradientAt F (G x) x` for a map
--   `G : H → H`, and convexity as `ConvexOn ℝ Set.univ F`; the space is a complete real
--   inner product space.
-- source:
--   Y. Nesterov, Lectures on Convex Optimization, 2nd ed., Springer 2018, Theorem 2.1.2; carved from the accepted proof of RelaxedPRS.Linear.theorem_4_3, https://prove2.me/submissions/23766413-5769-4c79-8267-9febba86ff5e

import Mathlib

set_option autoImplicit false
open scoped InnerProductSpace
open scoped RealInnerProductSpace

theorem Gradient.convex_first_order {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (hc : ConvexOn ℝ Set.univ F) (x y : E) : F x + ⟪G x, y - x⟫ ≤ F y := by sorry
