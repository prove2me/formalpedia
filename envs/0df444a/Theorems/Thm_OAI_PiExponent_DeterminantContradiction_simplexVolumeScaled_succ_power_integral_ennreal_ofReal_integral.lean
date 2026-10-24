-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_succ_power_integral_ennreal_ofReal_integral
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_power_integral_ennreal_ofReal_integral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:58:56.63668+00:00
-- url     : https://prove2.me/theorems/876aa2f4-e66f-4c8b-92bb-5b797a883b72
-- title:
--   Convert the ENNReal integral to a real integral
-- statement:
--   For natural `n` and `0 <= r`, the ENNReal integral over `[0,r]` equals the ENNReal cast of the corresponding real integral.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_power_integral_ennreal_ofReal_integral (n : Nat) (r : Real) (hr : 0 <= r) : MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) r)) (fun t : Real => ENNReal.ofReal ((r - t) ^ n / (Nat.factorial n : Real))) = ENNReal.ofReal (MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) r)) (fun t : Real => (r - t) ^ n / (Nat.factorial n : Real))) := by sorry
