-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexSlice_intervalIntegral_eval
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexSlice_intervalIntegral_eval
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:22:35.761515+00:00
-- url     : https://prove2.me/theorems/2e12aa33-bd13-4fa0-b0af-9f113e834c5f
-- title:
--   Evaluate the simplex power interval integral
-- statement:
--   The real interval integral of `(1 - t)^n / n!` over [0,1] is `1/(n+1)!`.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexSlice_intervalIntegral_eval (n : Nat) :
    ∫ t in (0 : Real)..1, (1 - t) ^ n / (n.factorial : Real) =
    1 / ((n + 1).factorial : Real) := by sorry
