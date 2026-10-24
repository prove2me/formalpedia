-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_integral_evaluation
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_integral_evaluation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:38:52.546318+00:00
-- url     : https://prove2.me/theorems/1081097a-5258-4169-88c0-f19e3be38d7d
-- title:
--   Evaluation of the simplex slice integral
-- statement:
--   For every ENNReal constant c, integrating the n-th power of the remaining slice radius over t ∈ [0,1] multiplies c by 1/(n+1). This is the ENNReal form of the elementary beta integral.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_integral_evaluation (n : Nat) (c : ENNReal) :
    (∫⁻ t in Set.Icc (0 : Real) 1,
        (ENNReal.ofReal (1 - t)) ^ n * c ∂MeasureTheory.volume) =
      c / (n + 1 : ENNReal) := by sorry
