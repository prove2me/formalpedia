-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexSlice_power_lintegral
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexSlice_power_lintegral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:16:08.936587+00:00
-- url     : https://prove2.me/theorems/dbf90b8b-07ef-4f8e-8a90-f87001b22910
-- title:
--   Integral of the simplex power profile
-- statement:
--   The lintegral over [0,1] of the ENNReal power profile (1 − t)^n/n! equals 1/(n+1)!.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexSlice_power_lintegral (n : Nat) :
    ∫⁻ t : Real,
      (if t ∈ Set.Icc (0 : Real) 1 then
        ENNReal.ofReal ((1 - t) ^ n / (n.factorial : Real))
      else 0) ∂MeasureTheory.volume =
    ENNReal.ofReal (1 / ((n + 1).factorial : Real)) := by sorry
