-- Prove2me | Theorems.Thm_Kyprianou_Ch04_generalLevyItoFormulaV3
-- name    : Kyprianou.Ch04.generalLevyItoFormulaV3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T15:14:08.610691+00:00
-- url     : https://prove2.me/theorems/78195916-e2a2-59d7-9a5b-b3c8e2819b23
-- title:
--   Theorem 4.3: general Levy Ito formula (corrected initial left value)
-- statement:
--   General Levy Ito formula with the initial left value equal almost surely to the initial process value, and the genuine uniform-in-probability stochastic integral definition.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, corrected initial condition.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.generalLevyItoFormulaV3
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (Xleft : NNReal -> Omega -> Real)
    (hLeftZero : ∀ᵐ omega ∂P, Xleft 0 omega = X 0 omega)
    (hLeft : ∀ᵐ omega : Omega ∂P,
      forall t : NNReal, 0 < t ->
        Tendsto (fun s : NNReal => X s omega)
          (nhdsWithin t (Set.Iio t))
          (nhds (Xleft t omega)))
    (f : Real × Real -> Real)
    (hfJointC1 : ContDiffOn Real 1 f
      (Set.prod (Set.Ici (0 : Real)) Set.univ))
    (hfSpaceC2 : forall s : NNReal,
      ContDiff Real 2 (fun x : Real => f ((s : Real), x)))
    (hfSpaceSecondContinuous :
      ContinuousOn
        (fun z : Real × Real =>
          iteratedDeriv 2 (fun x : Real => f (z.1, x)) z.2)
        (Set.prod (Set.Ici (0 : Real)) Set.univ))
    :
    ∃ (stochasticIntegral : NNReal -> Omega -> Real),
      IsStochasticIntegralInProbabilityV2 P X
        (fun s omega =>
          fderiv Real f ((s : Real), Xleft s omega) (0, 1))
        stochasticIntegral ∧
      (∀ᵐ omega : Omega ∂P, forall t : NNReal,
      f ((t : Real), X t omega) =
        f (0, X 0 omega) +
        (∫ s in Set.Icc (0 : Real) (t : Real),
          fderiv Real f ((s : Real), X (Real.toNNReal s) omega)
            (1, 0) ∂volume) +
        stochasticIntegral t omega +
        ((triplet.gaussianVariance : Real) / 2) *
          (∫ s in Set.Icc (0 : Real) (t : Real),
            iteratedDeriv 2
              (fun x : Real => f ((s : Real), x))
              (X (Real.toNNReal s) omega) ∂volume) +
        (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
            (Set.univ : Set Real),
          (f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
           f (z.1, Xleft (Real.toNNReal z.1) omega) -
           z.2 * fderiv Real f
             (z.1, Xleft (Real.toNNReal z.1) omega) (0, 1))
          ∂(pathJumpMeasure X Xleft omega))) := by sorry
