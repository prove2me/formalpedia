-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_base_case
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_base_case
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T03:02:01.700476+00:00
-- url     : https://prove2.me/theorems/d6a0b713-23e3-4cfb-a86e-72ad04d05bc3
-- title:
--   Unit simplex volume in dimension zero
-- statement:
--   The real volume of the nonnegative unit simplex in dimension zero is one.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_base_case :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ (1 : ℝ)}) =
    ((Nat.factorial 0 : ℕ) : ℝ)⁻¹ := by sorry
