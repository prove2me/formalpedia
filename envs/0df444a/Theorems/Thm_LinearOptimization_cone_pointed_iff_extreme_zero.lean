-- Prove2me | Theorems.Thm_LinearOptimization_cone_pointed_iff_extreme_zero
-- name    : LinearOptimization.cone_pointed_iff_extreme_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T20:47:58.473194+00:00
-- url     : https://prove2.me/theorems/22c841fa-457e-4343-b7ae-f4482f04b352
-- title:
--   Pointedness of a polyhedral cone: zero is an extreme point iff the cone contains no line
-- statement:
--   **(Theorem 4.12)** Let $C \subset \mathbb{R}^n$ be the polyhedral cone defined by the constraints $a_i'x \ge 0$, $i = 1, \dots, m$. Then, the following are equivalent:
--
--   - **(a)** the zero vector is an extreme point of $C$;
--   - **(b)** the cone $C$ does not contain a line;
--   - **(c)** there exist $n$ vectors out of the family $a_1, \dots, a_m$, which are linearly independent.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 4.12, p. 175

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_LinearOptimization_RecessionCone
import Definitions.Def_ContainsLine


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 4.12 (p. 175).** For the polyhedral cone
`C = {x | Ax ≥ 0}`, the following are equivalent: (a) `0` is an extreme
point of `C` (the cone is pointed); (b) `C` contains no line; (c) some
`n` of the constraint vectors `a₁, …, aₘ` are linearly independent. -/

theorem LinearOptimization.cone_pointed_iff_extreme_zero {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (IsPointedCone (polyhedron A 0) ↔ ¬ContainsLine (polyhedron A 0)) ∧
    (¬ContainsLine (polyhedron A 0) ↔
      ∃ s : Finset (Fin m), s.card = n ∧
        LinearIndependent ℝ (fun i : s => A i.1)) := by
  sorry
