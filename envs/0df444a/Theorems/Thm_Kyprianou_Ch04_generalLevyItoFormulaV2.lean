-- Prove2me | Theorems.Thm_Kyprianou_Ch04_generalLevyItoFormulaV2
-- name    : Kyprianou.Ch04.generalLevyItoFormulaV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T10:17:18.766577+00:00
-- url     : https://prove2.me/theorems/7db0519f-f23d-41fa-a53a-cf71674b4aa7
-- title:
--   Theorem 4.3: general Levy Ito formula with Gaussian and jump corrections (corrected v2)
-- statement:
--   For a general (not spectrally restricted) Levy process with an actual triplet and characteristic exponent, and a C^(1,2) time-space test function, the Ito identity includes the first time derivative, the genuinely constrained stochastic integral of the left-limit spatial derivative against X, the Gaussian-variance/2 second-spatial-derivative integral, and the raw jump-sum correction f(s,X_{s-}+delta)-f(s,X_{s-})-delta*fx(s,X_{s-}). The theorem asserts existence of an independently defined stochastic integral via convergence in probability of left-point sums, together with the complete Itô identity. Existence is a conclusion, not a premise. The source characteristic exponent convention is made explicit. The stochastic integral has UCP left-grid convergence.
-- source:
--   Kyprianou (2006), first edition, Theorem 4.3, printed page 94.

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

namespace Kyprianou.Ch04
theorem generalLevyItoFormulaV2
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
          ∂(pathJumpMeasure X Xleft omega))) := by
  sorry
end Kyprianou.Ch04
