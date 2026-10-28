-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexSlices_lintegral_eval
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexSlices_lintegral_eval
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:03:36.647462+00:00
-- url     : https://prove2.me/theorems/17e4d6d2-e8af-4c8a-bca5-1890de47e162
-- title:
--   Evaluation of the simplex slice integral
-- statement:
--   Evaluate the ENNReal integral of the fibers by scaling the unit simplex by `1 - t` for `t ∈ [0,1]`, then convert the resulting nonnegative real interval integral to ENNReal. This child proves the scaling argument within its own proof and imports no proposed child.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexSlices_lintegral_eval (n : Nat) :
    (∫⁻ t : Real,
      (if t ∈ Set.Icc (0 : Real) 1 then
        MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
            (Finset.univ.sum fun i : Fin n => x i) ≤ 1 - t}
      else 0) ∂MeasureTheory.volume) =
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
          (Finset.univ.sum fun i : Fin n => x i) ≤ 1} *
        ENNReal.ofReal (∫ t in (0 : Real)..1, (1 - t) ^ n) := by sorry
