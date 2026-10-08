-- Prove2me | Theorems.Thm_MatousekLP_SmallestBall_first_order_optimality
-- name    : MatousekLP.SmallestBall.first_order_optimality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T21:32:48.797833+00:00
-- url     : https://prove2.me/theorems/926ff19c-3bff-4e96-87dc-292855b58e74
-- title:
--   Fact 8.7.1 — first-order optimality criterion for a convex function on a convex set
-- statement:
--   Let $C\subseteq\mathbb{R}^n$ be a convex set and $f:\mathbb{R}^n\to\mathbb{R}$ a differentiable convex function, and let $x^*\in C$. Write $\nabla f(x^*)$ for the gradient of $f$ at $x^*$, viewed as a row vector, so that $\nabla f(x^*)(x-x^*)$ is its scalar product with $x-x^*$. Then $x^*$ minimizes $f$ over $C$, that is, $f(x^*)\le f(x)$ for all $x\in C$, if and only if
--   $$\nabla f(x^*)(x-x^*)\ \ge\ 0\qquad\text{for all } x\in C .$$
--
--   This is the variational inequality characterizing minimizers of a convex differentiable function over a convex set. It is the bridge from convex programming to linear programming used in the proof of the Karush–Kuhn–Tucker conditions (Proposition 8.7.2).
--
--   **Formalization Note** $\nabla f(x^*)(x-x^*)$ is the Fréchet derivative of $f$ at $x^*$ applied to $x-x^*$. The book's phrase "a vector $x^*$ minimizes $f(x)$ over $C$" includes $x^*\in C$; this membership is a hypothesis.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 186, Fact 8.7.1

import Mathlib

namespace MatousekLP.SmallestBall

/-- Fact 8.7.1 (Matoušek & Gärtner, p. 186). Let `C ⊆ ℝⁿ` be convex and `f : ℝⁿ → ℝ`
differentiable and convex, and let `x* ∈ C`. Then `x*` minimizes `f` over `C` if and only if
`∇f(x*)(x − x*) ≥ 0` for all `x ∈ C`; here `∇f(x*)(x − x*)` is the derivative of `f` at `x*`
applied to `x − x*`. -/
theorem first_order_optimality {n : ℕ} (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (f : (Fin n → ℝ) → ℝ) (hf : Differentiable ℝ f) (hfc : ConvexOn ℝ Set.univ f)
    (xstar : Fin n → ℝ) (hxstar : xstar ∈ C) :
    IsMinOn f C xstar ↔ ∀ x ∈ C, 0 ≤ fderiv ℝ f xstar (x - xstar) := by sorry

end MatousekLP.SmallestBall
