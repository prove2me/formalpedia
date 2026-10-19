-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_unit_volume_base
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_base
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T22:01:13.186662+00:00
-- url     : https://prove2.me/theorems/1f19e2c0-4a19-4280-89c7-cca57f7f7bba
-- title:
--   Zero-dimensional unit simplex volume
-- statement:
--   The zero-dimensional simplex has volume one: its defining conditions hold vacuously, and its ambient function space is a singleton of volume one.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_base :
    (MeasureTheory.volume
      {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ 1}).toReal =
      (Nat.factorial 0 : ℝ)⁻¹ := by sorry
