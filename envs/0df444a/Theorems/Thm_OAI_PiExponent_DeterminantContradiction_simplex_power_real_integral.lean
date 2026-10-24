-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_power_real_integral
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_power_real_integral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:45:41.385239+00:00
-- url     : https://prove2.me/theorems/cba299c2-94fb-4b9b-a031-77afc1661f17
-- title:
--   Evaluate the normalized cutoff power integral
-- statement:
--   Evaluate the ordinary integral of the cutoff normalized power. Restrict to `[0,T]`, substitute `u = (T-t)/T`, and evaluate the resulting power integral on `[0,1]`; the strict cutoff at `T` changes no integral value.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open scoped BigOperators
open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.simplex_power_real_integral (m : Nat) (T : Real) (hT : 0 < T) :
    MeasureTheory.integral MeasureTheory.volume (fun t : Real =>
      if 0 ≤ t ∧ t < T then ((T - t) / T) ^ m else 0) =
      T / ((m + 1 : Nat) : Real) := by sorry
