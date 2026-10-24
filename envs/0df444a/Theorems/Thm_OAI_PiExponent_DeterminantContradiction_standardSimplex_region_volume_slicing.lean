-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_region_volume_slicing
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_region_volume_slicing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:21:16.117345+00:00
-- url     : https://prove2.me/theorems/d86c0a8c-3beb-40a1-bec6-940f1c7b00c1
-- title:
--   Slice the standard simplex by its last coordinate
-- statement:
--   The volume of the (m+1)-dimensional simplex of radius H equals the interval integral of the volumes of its m-dimensional slices, parametrized by the last coordinate t.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_region_volume_slicing (m : Nat) (H : Real) (hH : 0 < H) :
    (MeasureTheory.volume {x : Fin (m + 1) → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H}).toReal =
      ∫ t in (0 : Real)..H,
        (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H - t}).toReal := by sorry
