-- Prove2me | Theorems.Thm_LinearOptimization_simplex_lexicographic_pivot_step
-- name    : LinearOptimization.simplex_lexicographic_pivot_step
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-06T03:25:36.614285+00:00
-- url     : https://prove2.me/theorems/4cbac0d6-726e-48a5-9fc6-98082148af28
-- title:
--   A lexicographic simplex pivot preserves positive rows and increases the zeroth row
-- statement:
--   Consider one iteration of the simplex method for the standard-form problem $\min c^{\mathsf T}x$ subject to $Ax=b$ and $x\ge 0$. Let $B$ be the current basis, let every nonzeroth row of its tableau
--
--   $$
--   \left[\,B^{-1}b\mid B^{-1}A\,\right]
--   $$
--
--   be lexicographically positive, and perform a pivot according to the lexicographic pivoting rule, producing the new basis $B'$.
--
--   Then every nonzeroth row of the new tableau is lexicographically positive, and the new zeroth row
--
--   $$
--   \left[\,-c_{B'}^{\mathsf T}(B')^{-1}b\mid
--   c^{\mathsf T}-c_{B'}^{\mathsf T}(B')^{-1}A\,\right]
--   $$
--
--   is strictly lexicographically larger than the old zeroth row.
--
--   This is the one-iteration invariant underlying lexicographic anticycling; iterating it and using the finiteness of the set of bases yields finite termination.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 3.4(a,b), p. 110, especially Eq. (3.5). https://studylib.net/doc/28617911/bertsimas-linear-cap-1-a-5

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_LinearOptimization_SimplexPivot

open Matrix

theorem LinearOptimization.simplex_lexicographic_pivot_step {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hA : LinearIndependent ℝ (fun i => A i))
    (B B' : Fin m ↪ Fin n) (x x' : Fin n → ℝ)
    (hstate : IsSimplexState A b B x)
    (hpos : ∀ i, LexPos (tableauRow A b B i))
    (hpivot : IsLexicographicPivot A b c B x B' x') :
    (∀ i, LexPos (tableauRow A b B' i)) ∧
      LexLt (tableauZerothRow A b c B) (tableauZerothRow A b c B') := by
  sorry
