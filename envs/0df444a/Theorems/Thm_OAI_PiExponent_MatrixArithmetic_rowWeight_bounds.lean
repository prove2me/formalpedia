-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixArithmetic_rowWeight_bounds
-- name    : OAI.PiExponent.MatrixArithmetic.rowWeight_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:36:51.000413+00:00
-- url     : https://prove2.me/theorems/7556622e-0668-4537-9042-45a4d3052191
-- title:
--   Bounds for the transverse weight of one row
-- statement:
--   Every row in the strict weighted simplex has nonnegative transverse weight, and that weight is at most theta times H. Positivity of the logarithmic weights follows from q i ≥ 2; the strict row budget bounds the transverse contribution after the nonnegative zeroth-coordinate contribution is discarded.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_FiniteMinorComparison

open OAI.PiExponent
open scoped BigOperators

theorem OAI.PiExponent.MatrixArithmetic.rowWeight_bounds
    (m K : ℕ) (v0 theta H : ℝ) (q : Fin m → ℕ)
    (hK : 0 < K) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hH : 0 < H) (hq : ∀ i, 2 ≤ q i)
    (ρ : OAI.PiExponent.InterpolationMatrix.Row K v0 theta
      (OAI.PiExponent.MatrixArithmetic.logWeights q) H) :
    0 ≤ ∑ i : Fin m, (ρ.2.1 i.succ : ℝ) *
        OAI.PiExponent.MatrixArithmetic.logWeights q i ∧
      (∑ i : Fin m, (ρ.2.1 i.succ : ℝ) *
        OAI.PiExponent.MatrixArithmetic.logWeights q i) ≤ theta * H := by sorry
