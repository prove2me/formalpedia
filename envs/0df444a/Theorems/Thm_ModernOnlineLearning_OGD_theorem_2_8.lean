-- Prove2me | Theorems.Thm_ModernOnlineLearning_OGD_theorem_2_8
-- name    : ModernOnlineLearning.OGD.theorem_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:35:41.660007+00:00
-- url     : https://prove2.me/theorems/f72306e6-d1f4-46d9-b727-aa0927e48bf5
-- title:
--   Theorem 2.8 — first-order optimality on a convex set
-- statement:
--   Let $V$ be a nonempty convex subset of a real inner-product space, let $x^\star\in V$, and let $f$ be convex and differentiable on an open set containing $V$. Then
--   $$x^\star\in\operatorname*{argmin}_{x\in V}f(x)\quad\Longleftrightarrow\quad\langle\nabla f(x^\star),y-x^\star\rangle\ge0\quad\text{for every }y\in V.$$
--
--   This condition characterizes constrained minima through feasible first-order directions and is used to analyze Euclidean projection.
--
--   **Formalization Note** The ambient space is a complete real inner-product space; the chapter's proof is dimension independent.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 2.8, p. 11

import Mathlib

namespace ModernOnlineLearning.OGD

/-- Orabona, Theorem 2.8, p. 11: first-order condition for a differentiable
convex function on a convex feasible set. -/
theorem theorem_2_8 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (V : Set E) (hV : V.Nonempty) (hconv : Convex ℝ V)
    (f : E → ℝ) (xstar : E) (hx : xstar ∈ V)
    (hopen : ∃ U : Set E, IsOpen U ∧ V ⊆ U ∧ ConvexOn ℝ U f ∧ DifferentiableOn ℝ f U) :
    (∀ y ∈ V, f xstar ≤ f y) ↔
      ∀ y ∈ V, 0 ≤ inner ℝ (gradient f xstar) (y - xstar) := by sorry

end ModernOnlineLearning.OGD
