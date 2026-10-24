-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixArithmetic_rowWeight_bounds_of_nonneg_weights
-- name    : OAI.PiExponent.MatrixArithmetic.rowWeight_bounds_of_nonneg_weights
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:46:07.372576+00:00
-- url     : https://prove2.me/theorems/840bfa0f-0cf5-4332-965a-eef39729148c
-- title:
--   Bounds for a row with nonnegative weights
-- statement:
--   For any nonnegative transverse weights, a row in the strict weighted simplex has nonnegative transverse weight at most theta times H. Unfolding the row weights expresses the simplex budget as a positive zeroth-coordinate contribution plus the transverse sum divided by theta; strict membership gives the upper bound, while nonnegative exponents and weights give the lower bound. The hK and hH assumptions are retained to match the target context; this argument only needs the stated positivity of v0 and theta.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_FiniteMinorComparison

open OAI.PiExponent
open scoped BigOperators

theorem OAI.PiExponent.MatrixArithmetic.rowWeight_bounds_of_nonneg_weights
    (m K : ℕ) (v0 theta H : ℝ) (w : Fin m → ℝ)
    (hK : 0 < K) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hH : 0 < H) (hw : ∀ i, 0 ≤ w i)
    (ρ : OAI.PiExponent.InterpolationMatrix.Row K v0 theta w H) :
    0 ≤ ∑ i : Fin m, (ρ.2.1 i.succ : ℝ) * w i ∧
      (∑ i : Fin m, (ρ.2.1 i.succ : ℝ) * w i) ≤ theta * H := by sorry
