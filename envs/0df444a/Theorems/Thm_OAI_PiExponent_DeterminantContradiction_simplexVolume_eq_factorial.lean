-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_eq_factorial
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_factorial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T02:25:30.610698+00:00
-- url     : https://prove2.me/theorems/b654c5d5-0813-41d0-a7ee-449a564e2193
-- title:
--   Unit simplex volume is the reciprocal factorial
-- statement:
--   The real volume of the nonnegative unit simplex in `Fin n → ℝ` is the reciprocal of `n!`. This includes `n = 0`, where the zero-dimensional simplex has volume `1`. A proof can proceed by dimension induction, slicing in one coordinate and applying Fubini/Tonelli and the scaling law for volume.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_factorial (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) =
    (Nat.factorial n : ℝ)⁻¹ := by sorry
