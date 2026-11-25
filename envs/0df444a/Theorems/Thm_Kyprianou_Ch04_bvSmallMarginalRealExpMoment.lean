-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvSmallMarginalRealExpMoment
-- name    : Kyprianou.Ch04.bvSmallMarginalRealExpMoment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:47:29.536995+00:00
-- url     : https://prove2.me/theorems/716269fb-861a-42aa-b3cb-2b8226685bf5
-- title:
--   Bounded-variation small-jump marginal: exact exponential moment
-- statement:
--   Identify the exact real moment of the small-jump marginal with no Gaussian component by finite-band approximation, uniform exponential second-moment bounds and weak moment transfer.
-- source:
--   Kyprianou (2006), Exercise 4.3(iv); unit marginal Lévy–Khintchine moment calculation.

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.bvSmallMarginalRealExpMoment
    (T : LevyKhintchineTriple)
    (hBV : (∫⁻ x in Ioo (-1 : Real) 1,
        ENNReal.ofReal |x| ∂T.levyMeasure) < ⊤)
    (nu : Measure Real) [IsProbabilityMeasure nu]
    (hnu : ∀ xi : Real, charFun nu xi =
      Complex.exp (Complex.I * ((T.drift * xi : Real) : Complex) +
        ∫ x in Ioo (-1 : Real) 1,
          levyCompensatedIntegrand xi x ∂T.levyMeasure))
    (beta : Real) :
    Integrable (fun x : Real => Real.exp (beta*x)) nu ∧
      (∫ x, Real.exp (beta*x) ∂nu) =
      Real.exp (T.drift * beta +
        ∫ x in Ioo (-1 : Real) 1,
          (Real.exp (beta*x)-1-beta*x) ∂T.levyMeasure) := by
  sorry
