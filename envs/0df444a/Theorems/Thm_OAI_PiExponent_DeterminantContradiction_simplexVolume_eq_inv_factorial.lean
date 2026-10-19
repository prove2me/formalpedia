-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_eq_inv_factorial
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_inv_factorial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T02:54:22.026065+00:00
-- url     : https://prove2.me/theorems/1377f235-8afe-4e0d-9fa5-d5a2e4ae76c4
-- title:
--   Unit simplex volume closed form
-- statement:
--   For every natural dimension `n`, the real volume of the nonnegative unit simplex in `Fin n → ℝ` equals the reciprocal of `n!`. This includes `n = 0`, where the simplex consists of the unique point in the zero-dimensional space and has volume `1`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_inv_factorial (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) =
    ((Nat.factorial n : ℕ) : ℝ)⁻¹ := by sorry
