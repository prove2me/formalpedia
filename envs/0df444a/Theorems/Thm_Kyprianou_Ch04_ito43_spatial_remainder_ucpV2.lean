-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_spatial_remainder_ucpV2
-- name    : Kyprianou.Ch04.ito43_spatial_remainder_ucpV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:11:10.806746+00:00
-- url     : https://prove2.me/theorems/ea90cb09-ebe2-56d6-b4b6-2c17e0befa58
-- title:
--   Spatial Taylor remainder convergence with correct initial left value
-- statement:
--   The spatial Taylor remainder converges uniformly in probability, with the initial left value equal almost surely to the initial process value.
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
open Kyprianou.Ch04

theorem Kyprianou.Ch04.ito43_spatial_remainder_ucpV2
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
    ∀ (T : NNReal) (epsilon : Real), 0 < epsilon →
    Tendsto (fun n : Nat =>
      (P {omega : Omega | ∃ t : NNReal, t ≤ T ∧
        let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
        let v : ℕ → NNReal := fun k => min t (u k)
        epsilon ≤ abs (((triplet.gaussianVariance : Real) / 2) *
          (∫ s in Set.Icc (0 : Real) (t : Real),
            iteratedDeriv 2 (fun x : Real => f ((s : Real), x))
              (X (Real.toNNReal s) omega) ∂volume) + (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
            (Set.univ : Set Real),
          (f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
           f (z.1, Xleft (Real.toNNReal z.1) omega) -
           z.2 * fderiv Real f
             (z.1, Xleft (Real.toNNReal z.1) omega) (0, 1))
          ∂(pathJumpMeasure X Xleft omega)) - (∑ k ∈ Finset.range n,
          (f ((v k : Real), X (v (k+1)) omega) -
          f ((v k : Real), X (v k) omega) -
          fderiv Real f ((u k : Real), Xleft (u k) omega) (0, 1) *
            (X (v (k+1)) omega - X (v k) omega))))}).toReal)
      atTop (nhds 0) := by sorry
