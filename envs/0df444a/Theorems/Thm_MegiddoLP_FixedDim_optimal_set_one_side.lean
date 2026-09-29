-- Prove2me | Theorems.Thm_MegiddoLP_FixedDim_optimal_set_one_side
-- name    : MegiddoLP.FixedDim.optimal_set_one_side
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:11:34.090817+00:00
-- url     : https://prove2.me/theorems/dfd51f2d-e89c-4425-9bbc-2a3ba6004e1e
-- title:
--   If a hyperplane contains no optimal point, all optimal points lie on one side of it
-- statement:
--   Consider the linear program
--
--   $$\text{minimize } c^Tx\quad\text{subject to } Ax\ge b,\qquad A\in\mathbb{R}^{n\times d},$$
--
--   and a hyperplane $\{x: a^Tx=\beta\}$ that contains no optimal solution of the program. Then either every optimal solution satisfies $a^Tx<\beta$, or every optimal solution satisfies $a^Tx>\beta$.
--
--   The set of optimal solutions is convex, which gives the claim. It means that the oracle's answer for such a hyperplane does not depend on which optimal solution is taken as $x^*$. So Megiddo's pruning is valid even when the program has multiple optima.
--
--   **Formalization Note** "Optimal" is `IsLpOptimal c (polyhedron A b)`: feasible and of least cost among feasible points. If the program has no optimal solution, both alternatives hold vacuously.
-- source:
--   Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, J. ACM 31(1) (1984) 114–127, §4, p. 123 (validity with multiple optima)

import Mathlib
import Definitions.Def_Polyhedron

/-!
Megiddo, J. ACM 31 (1984), §4 p. 123: if a hyperplane contains no optimal point of a linear
program, all optimal points lie on one side of it (convexity of the optimal set).
-/

open Matrix LinearOptimization

namespace MegiddoLP.FixedDim

/-- **Optimal points on one side.** For the program `minimize cᵀx subject to Ax ≥ b` and a
hyperplane `{a ⬝ᵥ x = β}` containing no optimal solution, either every optimal solution has
`a ⬝ᵥ x < β` or every optimal solution has `a ⬝ᵥ x > β`. -/
theorem optimal_set_one_side {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ)
    (c a : Fin d → ℝ) (β : ℝ)
    (hmiss : ∀ x, IsLpOptimal c (polyhedron A b) x → a ⬝ᵥ x ≠ β) :
    (∀ x, IsLpOptimal c (polyhedron A b) x → a ⬝ᵥ x < β) ∨
    (∀ x, IsLpOptimal c (polyhedron A b) x → β < a ⬝ᵥ x) := by sorry

end MegiddoLP.FixedDim
