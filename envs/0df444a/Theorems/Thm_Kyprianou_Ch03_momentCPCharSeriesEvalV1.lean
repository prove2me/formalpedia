-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentCPCharSeriesEvalV1
-- name    : Kyprianou.Ch03.momentCPCharSeriesEvalV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T13:16:06.534806+00:00
-- url     : https://prove2.me/theorems/2f19bd91-ba5b-411e-812c-f3004a7902d4
-- title:
--   Evaluate weighted characteristic-function power series
-- statement:
--   Sum the exponential series at charFun mu xi, then use integral subtraction and the constant integral to identify the exponent.
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8; decomposition of compound-Poisson characteristic function and compensated exponential kernel.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentCPCharSeriesEvalV1
    (mu : Measure Real) [IsFiniteMeasure mu] (xi : Real) :
    (∑' n : ℕ, ((Real.exp (-(mu Set.univ).toReal) : ℝ) : ℂ) *
        ((charFun mu xi) ^ n / (n.factorial : ℂ))) =
      Complex.exp (∫ x, (Complex.exp (Complex.I * (((xi * x : Real) : Complex))) - 1) ∂mu) := by sorry
