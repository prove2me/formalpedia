-- Prove2me | Theorems.Thm_JaggiFW_Sparsity_support_simplex
-- name    : JaggiFW.Sparsity.support_simplex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:04.240368+00:00
-- url     : https://prove2.me/theorems/9c410a03-aac9-4201-b734-ce03ac5ec7cb
-- title:
--   Table 1: the simplex support function is the largest coordinate
-- statement:
--   Let $n\ge1$ and $y\in\mathbb R^n$. The unit simplex $\Delta_n$ is the convex hull of the unit basis vectors $e_1,\dots,e_n$ (the atoms of this row), and its support function is attained and equals the largest coordinate of $y$:
--   $$
--   \max_{s\in\Delta_n}\sum_i s_i y_i=\max_i y_i.
--   $$
--   This identifies the linear subproblem used by a Frank–Wolfe step on the simplex.
--
--   **Formalization Note** The statement asserts an attaining coordinate and an attained maximum on the simplex. The table's $O(n)$ algorithmic cost is outside the mathematical claim.
-- source:
--   Jaggi, Revisiting Frank-Wolfe: Projection-Free Sparse Convex Optimization, ICML 2013 (JMLR W&CP 28), PDF p. 6, Table 1, simplex row

import Mathlib
import Definitions.Def_JaggiFW_Sparsity_Setting

namespace JaggiFW.Sparsity

/-- The simplex row of Table 1, PDF p. 6. -/
theorem support_simplex {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ) :
    stdSimplex ℝ (Fin n) = convexHull ℝ (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → ℝ)) ∧
    ∃ i : Fin n, (∀ j, y j ≤ y i) ∧
      IsGreatest ((fun s => ∑ j, s j * y j) '' stdSimplex ℝ (Fin n)) (y i) := by sorry

end JaggiFW.Sparsity
