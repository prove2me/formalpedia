-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexSlices_scalar_lintegral
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexSlices_scalar_lintegral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:07:33.796637+00:00
-- url     : https://prove2.me/theorems/c78844ce-710b-4fad-be5e-a696662b15c9
-- title:
--   Scalar interval integral conversion
-- statement:
--   The `ENNReal` integral over the real line of the interval-restricted scalar function equals the scalar times the `ENNReal.ofReal` interval integral. The power is nonnegative on `[0,1]`, so this follows from the indicator-function integral formula and the conversion between a nonnegative real integral and its `ENNReal` integral.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexSlices_scalar_lintegral (n : Nat) (c : ENNReal) :
    (∫⁻ t : Real,
      (if t ∈ Set.Icc (0 : Real) 1 then
        c * ENNReal.ofReal ((1 - t) ^ n)
      else 0) ∂MeasureTheory.volume) =
      c * ENNReal.ofReal (∫ t in (0 : Real)..1, (1 - t) ^ n) := by sorry
