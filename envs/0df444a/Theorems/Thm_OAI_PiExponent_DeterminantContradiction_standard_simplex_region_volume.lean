-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standard_simplex_region_volume
-- name    : OAI.PiExponent.DeterminantContradiction.standard_simplex_region_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T02:58:38.020093+00:00
-- url     : https://prove2.me/theorems/b8b98e0b-1bb8-4613-8654-830cd0d262ee
-- title:
--   Volume of the standard simplex region
-- statement:
--   For nonnegative cutoff T, the real-valued volume of the standard nonnegative simplex in dimension m is T^m divided by m factorial, including dimension zero and T = 0.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.standard_simplex_region_volume
    (m : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ T}) =
      T ^ m / (Nat.factorial m : ℝ) := by sorry
