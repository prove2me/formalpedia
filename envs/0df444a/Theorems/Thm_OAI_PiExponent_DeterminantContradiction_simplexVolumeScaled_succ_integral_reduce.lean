-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_succ_integral_reduce
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_integral_reduce
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:43:41.091752+00:00
-- url     : https://prove2.me/theorems/1caf0cf2-268e-49f1-9305-fb753ecc4dc3
-- title:
--   Replace the simplex volume integrand using the lower-dimensional formula
-- statement:
--   Under the lower-dimensional volume formula, the integrand volume at residual scale r − t agrees with the stated ENNReal power on the interval 0 ≤ t ≤ r.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_integral_reduce
    (n : Nat) (r : Real) (hr : 0 ≤ r)
    (ih : ∀ s : Real, 0 ≤ s →
      MeasureTheory.volume
          {y : Fin n → Real | (∀ j, 0 ≤ y j) ∧ (∑ j, y j) ≤ s} =
        ENNReal.ofReal (s ^ n / (Nat.factorial n : Real))) :
    (∫⁻ t in Set.Icc (0 : Real) r,
        MeasureTheory.volume
          {y : Fin n → Real | (∀ j, 0 ≤ y j) ∧ (∑ j, y j) ≤ r - t}
        ∂MeasureTheory.volume) =
      (∫⁻ t in Set.Icc (0 : Real) r,
        ENNReal.ofReal ((r - t) ^ n / (Nat.factorial n : Real))
        ∂MeasureTheory.volume) := by sorry
