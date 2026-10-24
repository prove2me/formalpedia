-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_region_volume_integral
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_region_volume_integral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:22:22.184326+00:00
-- url     : https://prove2.me/theorems/4afcea88-bd73-490b-8ed4-e4f325d3927a
-- title:
--   Evaluate the integral of the lower-dimensional simplex volumes
-- statement:
--   Assuming the m-dimensional volume formula for every positive radius, the interval integral of the m-dimensional slice volumes at radius H - t is the claimed (m+1)-dimensional formula.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_region_volume_integral (m : Nat) (H : Real) (hH : 0 < H)
    (ih : ∀ (T : Real), 0 < T →
      (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ T}).toReal =
        T ^ m / ((Nat.factorial m : Nat) : Real)) :
    (∫ t in (0 : Real)..H,
      (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H - t}).toReal) =
      H ^ (m + 1) / ((Nat.factorial (m + 1) : Nat) : Real) := by sorry
