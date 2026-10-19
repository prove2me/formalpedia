-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standard_simplex_volume_zero
-- name    : OAI.PiExponent.DeterminantContradiction.standard_simplex_volume_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T22:15:43.355352+00:00
-- url     : https://prove2.me/theorems/00ae5797-15e4-4f89-ad59-89d8cc5616cb
-- title:
--   Zero-dimensional standard simplex volume
-- statement:
--   The zero-dimensional standard simplex has volume one, equal to the reciprocal of zero factorial. This supplies the induction base.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.standard_simplex_volume_zero :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ (1 : ℝ)}) =
      1 / (Nat.factorial 0 : ℝ) := by sorry
