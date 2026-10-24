-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_power_lintegral_eq_ofReal_integral
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_power_lintegral_eq_ofReal_integral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:45:28.193576+00:00
-- url     : https://prove2.me/theorems/8087d3d5-ce35-457d-9063-e4b59b198e06
-- title:
--   Convert the cutoff lintegral to a real integral
-- statement:
--   Convert the extended-real integral of the cutoff function to the ofReal of its ordinary real integral. Prove integrability from boundedness and compact support, establish nonnegativity, and apply the lintegral/ofReal integral bridge.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open scoped BigOperators
open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.simplex_power_lintegral_eq_ofReal_integral (m : Nat) (T : Real) (hT : 0 < T) :
    MeasureTheory.lintegral MeasureTheory.volume (fun t : Real =>
      if 0 ≤ t ∧ t < T then ENNReal.ofReal (((T - t) / T) ^ m)
      else 0) =
      ENNReal.ofReal (MeasureTheory.integral MeasureTheory.volume (fun t : Real =>
        if 0 ≤ t ∧ t < T then ((T - t) / T) ^ m else 0)) := by sorry
