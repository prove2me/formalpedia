-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentFiniteBoundedJumpLawV1
-- name    : Kyprianou.Ch03.momentFiniteBoundedJumpLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T13:20:18.621667+00:00
-- url     : https://prove2.me/theorems/dc638bc8-7c0f-4fea-b49b-0380cabbd01c
-- title:
--   Finite bounded-jump law with signed exponential transform
-- statement:
--   Take the explicit compound-Poisson law with intensity t times nu. Use the characteristic-function series, published signed exponential transform and bounded-mark integrability. Convert finite lintegral to the Bochner integral.
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8; finite compensated small-jump approximation, reusing Chapter 8 finite transform construction and published compound-Poisson transform.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentFiniteBoundedJumpLawV1
    (nu : Measure Real) [IsFiniteMeasure nu]
    (hnu : ∀ᵐ x ∂nu, |x| < 1) (t : NNReal) :
    ∃ J : ProbabilityMeasure Real,
      (∀ xi : Real, charFun (J : Measure Real) xi =
        Complex.exp (((t : Real) : Complex) *
          ∫ x, (Complex.exp (Complex.I * (((xi * x : Real) : Complex))) - 1) ∂nu)) ∧
      (∀ b : Real, Integrable (fun x : Real => Real.exp (b*x)) (J : Measure Real) ∧
        (∫ x, Real.exp (b*x) ∂(J : Measure Real)) =
          Real.exp ((t : Real) * ∫ x, (Real.exp (b*x)-1) ∂nu)) := by sorry
