-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexSlice_lintegral_eq_factorial
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexSlice_lintegral_eq_factorial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:07:43.664892+00:00
-- url     : https://prove2.me/theorems/dec56019-dd5d-4681-811e-5171766eed72
-- title:
--   Integral of simplex slice volumes
-- statement:
--   The lintegral of the n-dimensional simplex slice volumes over t in [0,1] equals 1/(n+1)!. Prove using the cutoff-volume formula to rewrite the integrand as (1-t)^n/n! on [0,1], then evaluate the elementary power integral. The endpoints, including n=0, are covered by the stated formula.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexSlice_lintegral_eq_factorial (n : Nat) :
    ∫⁻ t : Real,
      (if t ∈ Set.Icc (0 : Real) 1 then
        MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
            (Finset.univ.sum fun i : Fin n => x i) ≤ 1 - t}
      else 0) ∂MeasureTheory.volume =
    ENNReal.ofReal (1 / ((n + 1).factorial : Real)) := by sorry
