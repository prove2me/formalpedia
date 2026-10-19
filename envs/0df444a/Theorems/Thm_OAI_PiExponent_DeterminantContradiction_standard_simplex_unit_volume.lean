-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standard_simplex_unit_volume
-- name    : OAI.PiExponent.DeterminantContradiction.standard_simplex_unit_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:14:13.747926+00:00
-- url     : https://prove2.me/theorems/65c00b67-5664-42a3-af29-db087f32464f
-- title:
--   Volume of the unit standard simplex
-- statement:
--   The unit standard simplex in dimension m has volume 1 divided by m factorial. In dimension zero, the region is a singleton and both sides are 1.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.standard_simplex_unit_volume
    (m : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ (1 : ℝ)}) =
      1 / (Nat.factorial m : ℝ) := by sorry
