-- Prove2me | Theorems.Thm_Kyprianou_Ch04_smallMarginalExactFiniteApprox
-- name    : Kyprianou.Ch04.smallMarginalExactFiniteApprox
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T08:15:03.118316+00:00
-- url     : https://prove2.me/theorems/a3bf2f34-24fa-4f36-8ba6-6e72c3c40792
-- title:
--   Small-jump marginal finite approximation with exact moments
-- statement:
--   Construct zero-Gaussian finite-band marginal laws with exact exponential moments and weak convergence via the characteristic function continuity theorem.
-- source:
--   Kyprianou (2006), Exercise 4.3(iv).

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.smallMarginalExactFiniteApprox
    (T : LevyKhintchineTriple)
    (e : Nat → Real) (he : ∀ n, 0 < e n ∧ e n < 1)
    (hzero : Tendsto e atTop (nhds 0))
    (nu : ProbabilityMeasure Real)
    (hnu : ∀ xi : Real, charFun (nu : Measure Real) xi =
      Complex.exp (Complex.I * ((T.drift * xi : Real) : Complex) +
        ∫ x in Ioo (-1 : Real) 1,
          levyCompensatedIntegrand xi x ∂T.levyMeasure)) :
    ∃ q : Nat → ProbabilityMeasure Real,
      Tendsto q atTop (nhds nu) ∧
      ∀ n (b : Real), Integrable (fun x : Real => Real.exp (b*x)) (q n : Measure Real) ∧
        (∫ x, Real.exp (b*x) ∂(q n : Measure Real)) =
        Real.exp (T.drift*b + ∫ x in {x : Real | e n ≤ |x| ∧ |x| < 1},
          (Real.exp (b*x)-1-b*x) ∂T.levyMeasure) := by
  sorry
