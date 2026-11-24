-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentLightMarginalExpAbsV1
-- name    : Kyprianou.Ch03.momentLightMarginalExpAbsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T12:30:33.750271+00:00
-- url     : https://prove2.me/theorems/0f7412ab-6d9b-475d-a824-3d08d9264198
-- title:
--   All absolute exponential moments of the Gaussian plus small-jump marginal
-- statement:
--   Approximate the compensated small-jump law by finite annular compound-Poisson laws. The quadratic bound on e^(±b x)-1∓b x on the unit ball and the Lévy-measure square integrability yield a uniform exponential moment bound. Include the finite Gaussian and drift exponential factors. Weak convergence via the characteristic functions and lower semicontinuity transfer the bound, then use exp(b |x|)≤exp(b x)+exp(-b x).
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8; shared reduction of submulMoment_forward and submulMoment_reverse.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentLightMarginalExpAbsV1
    (T : ProbabilityTheory.LevyKhintchineTriple) (t : NNReal) (ht : 0 < t)
    (nu : Measure Real) [IsProbabilityMeasure nu]
    (hnu : ∀ xi : Real, charFun nu xi = Complex.exp (((t : Real) : Complex) *
          (Complex.I * ((T.drift * xi : Real) : Complex) -
          (((T.gaussianVariance : Real) * xi ^ 2 / 2 : Real) : Complex) +
          ∫ x in Set.Ioo (-1 : Real) 1,
            ProbabilityTheory.levyCompensatedIntegrand xi x ∂T.levyMeasure)))
    (b : Real) (hb : 0 < b) :
    Integrable (fun x : Real => Real.exp (b * |x|)) nu := by sorry
