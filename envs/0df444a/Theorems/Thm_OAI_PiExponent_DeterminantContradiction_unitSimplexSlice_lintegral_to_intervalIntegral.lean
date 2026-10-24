-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexSlice_lintegral_to_intervalIntegral
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexSlice_lintegral_to_intervalIntegral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:21:25.415738+00:00
-- url     : https://prove2.me/theorems/a240a685-a33e-4023-bd54-51792750d6cb
-- title:
--   Convert the simplex profile lintegral to an interval integral
-- statement:
--   The nonnegative ENNReal profile supported on [0,1] has lintegral equal to the ofReal of the corresponding real interval integral.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexSlice_lintegral_to_intervalIntegral (n : Nat) :
    ∫⁻ t : Real,
      (if t ∈ Set.Icc (0 : Real) 1 then
        ENNReal.ofReal ((1 - t) ^ n / (n.factorial : Real))
      else 0) ∂MeasureTheory.volume =
    ENNReal.ofReal (∫ t in (0 : Real)..1, (1 - t) ^ n / (n.factorial : Real)) := by sorry
