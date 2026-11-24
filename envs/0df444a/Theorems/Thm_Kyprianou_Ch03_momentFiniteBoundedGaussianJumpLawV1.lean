-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentFiniteBoundedGaussianJumpLawV1
-- name    : Kyprianou.Ch03.momentFiniteBoundedGaussianJumpLawV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T13:20:21.753725+00:00
-- url     : https://prove2.me/theorems/1c1f51e4-c657-41d1-a1ff-b84b43f183bc
-- title:
--   Compensated bounded-jump Gaussian marginal with exact transforms
-- statement:
--   Convolve the bounded-jump compound-Poisson law with Gaussian mean t*(d-∫x dnu) and variance t*v. On the support the compensated complex kernel subtracts I*xi*x. Multiply characteristic and signed exponential transforms and cancel the compensator shift.
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8; finite compensated small-jump approximation, reusing Chapter 8 finite transform construction and published compound-Poisson transform.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentFiniteBoundedGaussianJumpLawV1
    (nu : Measure Real) [IsFiniteMeasure nu]
    (hnu : ∀ᵐ x ∂nu, |x| < 1) (d : Real) (v t : NNReal) :
    ∃ Q : ProbabilityMeasure Real,
      (∀ xi : Real, charFun (Q : Measure Real) xi =
        Complex.exp (((t : Real) : Complex) *
          (Complex.I * ((d * xi : Real) : Complex) -
          (((v : Real) * xi ^ 2 / 2 : Real) : Complex) +
          ∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂nu))) ∧
      (∀ b : Real, Integrable (fun x : Real => Real.exp (b*x)) (Q : Measure Real) ∧
        (∫ x, Real.exp (b*x) ∂(Q : Measure Real)) =
          Real.exp ((t : Real) * (d*b + (v : Real)*b^2/2 +
            ∫ x, (Real.exp (b*x)-1-b*x) ∂nu))) := by sorry
