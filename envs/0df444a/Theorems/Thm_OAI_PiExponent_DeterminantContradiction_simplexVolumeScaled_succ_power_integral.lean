-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_succ_power_integral
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_power_integral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:43:54.662062+00:00
-- url     : https://prove2.me/theorems/64f93951-9eee-46ec-97d5-e99e07339285
-- title:
--   Evaluate the ENNReal integral of the residual power
-- statement:
--   For n ≥ 0 and r ≥ 0, integrate the nonnegative power (r − t)^n divided by n! over 0 ≤ t ≤ r and express the result using (n+1)! = (n+1)n!.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_power_integral
    (n : Nat) (r : Real) (hr : 0 ≤ r) :
    (∫⁻ t in Set.Icc (0 : Real) r,
        ENNReal.ofReal ((r - t) ^ n / (Nat.factorial n : Real))
        ∂MeasureTheory.volume) =
      ENNReal.ofReal (r ^ (n + 1) / (Nat.factorial (n + 1) : Real)) := by sorry
