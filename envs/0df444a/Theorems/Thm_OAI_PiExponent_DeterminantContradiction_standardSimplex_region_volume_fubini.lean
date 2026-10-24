-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_region_volume_fubini
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_region_volume_fubini
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:28:08.184034+00:00
-- url     : https://prove2.me/theorems/31f420cf-1a3f-4220-80b5-067be76516cd
-- title:
--   Express simplex volume as an integral of its fibers
-- statement:
--   The volume of the nonnegative simplex in `Fin (m + 1)` equals the integral over the last coordinate of the volumes of its fibers, including the last-coordinate nonnegativity constraint.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_region_volume_fubini (m : Nat) (H : Real) :
    (MeasureTheory.volume {x : Fin (m + 1) → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H}).toReal =
      ∫ t : Real,
        (MeasureTheory.volume {x : Fin m → Real | 0 ≤ t ∧ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H - t}).toReal := by sorry
