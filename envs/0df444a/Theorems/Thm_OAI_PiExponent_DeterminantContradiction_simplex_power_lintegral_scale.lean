-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_power_lintegral_scale
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_power_lintegral_scale
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:25:20.442633+00:00
-- url     : https://prove2.me/theorems/d50fd830-e565-4559-93bc-34512e55e96b
-- title:
--   Scaling the simplex slice integral by an extended-real volume
-- statement:
--   For any natural exponent, real cutoff, and extended-real constant, factoring that constant out of the integral of the nonnegative slice function gives the scalar integral multiplied by the constant.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators
open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.simplex_power_lintegral_scale (m : Nat) (T : Real) (V : ENNReal) :
    MeasureTheory.lintegral MeasureTheory.volume (fun t : Real =>
      if 0 ≤ t ∧ t < T then
        ENNReal.ofReal (((T - t) / T) ^ m) * V
      else 0) =
      (MeasureTheory.lintegral MeasureTheory.volume (fun t : Real =>
        if 0 ≤ t ∧ t < T then ENNReal.ofReal (((T - t) / T) ^ m)
        else 0)) * V := by sorry
