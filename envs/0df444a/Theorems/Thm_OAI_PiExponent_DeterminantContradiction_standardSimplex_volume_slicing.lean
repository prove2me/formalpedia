-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_volume_slicing
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_volume_slicing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:34:34.15902+00:00
-- url     : https://prove2.me/theorems/4e3a09b7-843b-4af2-afe7-5b70a1afd879
-- title:
--   Simplex region volume recurrence by slicing
-- statement:
--   Slicing the region by its last coordinate and integrating the volumes of the dilated lower-dimensional regions gives the volume recurrence vol(Sₙ₊₁) = vol(Sₙ)/(n+1). This removes the geometric part of the successor step from the parent.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_volume_slicing (n : Nat) :
    MeasureTheory.volume
        {y : Fin (n + 1) → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ 1} =
      MeasureTheory.volume
        {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ 1} / (n + 1 : ENNReal) := by sorry
