-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentSmallGaussianMarginalFiniteApproxV1
-- name    : Kyprianou.Ch03.momentSmallGaussianMarginalFiniteApproxV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T12:35:25.292658+00:00
-- url     : https://prove2.me/theorems/6f1c4d49-c451-43c1-a2e3-dc5b7c6e36da
-- title:
--   Finite compound-Poisson approximations with uniformly bounded signed exponential moments
-- statement:
--   Use the annular measure eps_n≤|x|<1, with eps_n tending to zero. Form its finite compound-Poisson distribution with intensity t times the restriction, shift by t times drift minus the compensating first moment, and convolve with the Gaussian variance t times T.gaussianVariance. The proved small-jump exponent band limit gives characteristic convergence. The exact compound-Poisson exponential transform and Gaussian exponential transform give a bound uniform in n by the integrable quadratic compensated exponential kernel.
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8: finite compound-Poisson law and exponential moment of the compensated small-jump law.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentSmallGaussianMarginalFiniteApproxV1
    (T : ProbabilityTheory.LevyKhintchineTriple) (t : NNReal) (ht : 0 < t) :
    ∃ q : ℕ → ProbabilityMeasure Real,
      (∀ xi : Real, Tendsto (fun n => charFun (q n : Measure Real) xi) atTop
        (𝓝 (Complex.exp (((t : Real) : Complex) *
          (Complex.I * ((T.drift * xi : Real) : Complex) -
          (((T.gaussianVariance : Real) * xi ^ 2 / 2 : Real) : Complex) +
          ∫ x in Set.Ioo (-1 : Real) 1,
            ProbabilityTheory.levyCompensatedIntegrand xi x ∂T.levyMeasure))))) ∧
      ∀ b : Real, ∃ C : ENNReal, C < ⊤ ∧
        ∀ n, (∫⁻ x, ENNReal.ofReal (Real.exp (b * x)) ∂(q n : Measure Real)) ≤ C := by sorry
