-- Prove2me | Theorems.Thm_MatousekLP_SmallestBall_kkt_conditions
-- name    : MatousekLP.SmallestBall.kkt_conditions
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T21:54:21.587577+00:00
-- url     : https://prove2.me/theorems/492aa346-e0fe-40d8-80d7-b6516f411bd3
-- title:
--   Proposition 8.7.2 — Karush–Kuhn–Tucker conditions for convex programs in equational form
-- statement:
--   Let $A$ be a real $m\times n$ matrix with columns $a_1,\dots,a_n$, let $b\in\mathbb{R}^m$, and let $f:\mathbb{R}^n\to\mathbb{R}$ be convex and differentiable with continuous partial derivatives. Consider the convex program
--   $$\text{minimize } f(x)\ \text{ subject to } Ax=b,\ x\ge 0 .$$
--   A feasible solution $x^*\in\mathbb{R}^n$ is optimal if and only if there is a vector $\tilde y\in\mathbb{R}^m$ such that for all $j\in\{1,\dots,n\}$,
--   $$\nabla f(x^*)_j+\tilde y^{T}a_j\ \begin{cases}=0 & \text{if } x^*_j>0,\\ \ge 0 & \text{otherwise.}\end{cases}$$
--   Here $\nabla f(x^*)_j=\partial f/\partial x_j$ at $x^*$. The components of $\tilde y$ are the Karush–Kuhn–Tucker multipliers.
--
--   The KKT conditions are the optimality certificate for convex programs; in this section they are the step that turns the smallest-ball program (8.15) into the geometry of Lemma 8.7.3.
--
--   **Formalization Note** $\nabla f(x^*)_j$ is the derivative of $f$ at $x^*$ applied to the $j$th unit vector, and $\tilde y^Ta_j=\sum_i \tilde y_i A_{ij}$ is the $j$th entry of the row vector $\tilde y^TA$. "Continuous partial derivatives" is `ContDiff ℝ 1 f`. "Otherwise" is read as $x^*_j\not>0$, which for a feasible $x^*$ means $x^*_j=0$.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 187, Proposition 8.7.2 (Karush–Kuhn–Tucker conditions)

import Mathlib
import Definitions.Def_MatousekLP_SmallestBall_Basic

open Matrix

namespace MatousekLP.SmallestBall

/-- Proposition 8.7.2 (Karush–Kuhn–Tucker conditions; Matoušek & Gärtner, p. 187). Consider the
convex program "minimize `f(x)` subject to `Ax = b`, `x ≥ 0`" with `f` convex and differentiable
with continuous partial derivatives. A feasible `x*` is optimal iff there is `ỹ ∈ ℝ^m` such that
for all `j`, `∇f(x*)ⱼ + ỹᵀaⱼ = 0` if `x*ⱼ > 0` and `≥ 0` otherwise, where `aⱼ` is the `j`th column
of `A`. Here `∇f(x*)ⱼ = fderiv ℝ f x* (eⱼ)` and `ỹᵀaⱼ = ∑ᵢ ỹᵢ Aᵢⱼ = (ỹ ᵥ* A) j`. -/
theorem kkt_conditions {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (f : (Fin n → ℝ) → ℝ) (hfc : ConvexOn ℝ Set.univ f) (hf : ContDiff ℝ 1 f)
    (xstar : Fin n → ℝ) (hxstar : MatousekLP.BFS.IsFeasible A b xstar) :
    IsOptimal f A b xstar ↔
      ∃ y : Fin m → ℝ, ∀ j : Fin n,
        (0 < xstar j → fderiv ℝ f xstar (Pi.single j 1) + (y ᵥ* A) j = 0) ∧
        (¬ 0 < xstar j → 0 ≤ fderiv ℝ f xstar (Pi.single j 1) + (y ᵥ* A) j) := by sorry

end MatousekLP.SmallestBall
