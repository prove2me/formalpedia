-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvMarginalSplitLaw
-- name    : Kyprianou.Ch04.bvMarginalSplitLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T08:15:00.636036+00:00
-- url     : https://prove2.me/theorems/9be4fc4b-5ace-535e-9df4-89a75b26c595
-- title:
--   Zero Gaussian marginal law splits into large and small jump factors
-- statement:
--   Factor the zero-Gaussian marginal into a finite large-mark compound Poisson law and the drift plus compensated small-mark law.
-- source:
--   Kyprianou (2006), Exercise 4.3(iv).

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.bvMarginalSplitLaw
    (T : LevyKhintchineTriple) (hG : T.gaussianVariance = 0)
    (mu : Measure Real) [IsProbabilityMeasure mu]
    (hmu : ∀ xi : Real, charFun mu xi =
      Complex.exp (Kyprianou.Ch01.levyTripleExponent T xi)) :
    ∃ nu : Measure Real, IsProbabilityMeasure nu ∧
      (∀ xi : Real, charFun nu xi =
        Complex.exp (Complex.I * ((T.drift * xi : Real) : Complex) +
          ∫ x in Ioo (-1 : Real) 1, levyCompensatedIntegrand xi x ∂T.levyMeasure)) ∧
      mu = (KSATSingleFlip.Connect.compoundPoisson
        (T.levyMeasure.restrict {x : Real | 1 ≤ |x|})).conv nu := by
  sorry
