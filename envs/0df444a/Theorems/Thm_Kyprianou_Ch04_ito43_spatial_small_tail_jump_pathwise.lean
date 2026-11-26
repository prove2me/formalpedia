-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_spatial_small_tail_jump_pathwise
-- name    : Kyprianou.Ch04.ito43_spatial_small_tail_jump_pathwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:39:15.770131+00:00
-- url     : https://prove2.me/theorems/bf19113c-6ef0-4717-b455-f2efdedd7dfd
-- title:
--   Complementary Taylor jump integral bounded by squared actual jump energy
-- statement:
--   Complementary Taylor jump integral bounded by squared actual jump energy.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

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

theorem Kyprianou.Ch04.ito43_spatial_small_tail_jump_pathwise
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
    (H : NNReal) (M a : ℝ) (ha : 0 < a) (m : ℕ)
    (hcut : ∀ s ∈ Set.Icc (0 : ℝ) (H : ℝ),
      ∀ x ∈ Set.Icc (-M) M, ∀ y ∈ Set.Icc (-M) M,
        |(f (s,y)-f (s,x)-deriv (fun z : ℝ => f (s,z)) x*(y-x) -
          iteratedDeriv 2 (fun z : ℝ => f (s,z)) x*(y-x)^2/2) *
          (1-min 1 (max 0 (|y-x| *((m : ℝ)+1)-1)))| ≤ a*(y-x)^2)
    (omega : Omega)
    (hbounded : ∀ s : NNReal, s ≤ H → |X s omega| ≤ M)
    (hcad : IsCadlag (fun s : NNReal => X s omega))
    (hl : ∀ s : NNReal, 0 < s → Tendsto (fun r => X r omega)
      (nhdsWithin s (Set.Iio s)) (nhds (Xleft s omega)))
    (hE : Summable (fun s : Set.Ioc (0 : NNReal) H => (X s omega-Xleft s omega)^2))
    (t : NNReal) (ht : t ≤ H) :
    let chi : ℝ → ℝ := fun z => min 1 (max 0 (|z| * ((m : ℝ) + 1) - 1))
    |(∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
            (Set.univ : Set Real),
          (f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
           f (z.1, Xleft (Real.toNNReal z.1) omega) -
           z.2 * fderiv Real f
             (z.1, Xleft (Real.toNNReal z.1) omega) (0, 1))
          ∂(pathJumpMeasure X Xleft omega)) - (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
      iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) (Xleft (Real.toNNReal z.1) omega) * z.2^2 / 2 ∂(pathJumpMeasure X Xleft omega)) - (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
       (f (z.1,Xleft (Real.toNNReal z.1) omega + z.2) -
        f (z.1,Xleft (Real.toNNReal z.1) omega) -
        z.2 * fderiv ℝ f (z.1,Xleft (Real.toNNReal z.1) omega) (0,1) -
        iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) (Xleft (Real.toNNReal z.1) omega) * z.2^2 / 2)
          * chi z.2 ∂(pathJumpMeasure X Xleft omega))| ≤
      a*(∑' s : Set.Ioc (0 : NNReal) H, (X s omega-Xleft s omega)^2) := by sorry
