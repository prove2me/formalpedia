-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_spatial_small_tail_grid_pathwise
-- name    : Kyprianou.Ch04.ito43_spatial_small_tail_grid_pathwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:39:11.347042+00:00
-- url     : https://prove2.me/theorems/35247332-802e-5549-83ef-67c119a64cb0
-- title:
--   Complementary Taylor grid sum bounded by stopped grid energy
-- statement:
--   Complementary Taylor grid sum bounded by stopped grid energy.
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

theorem Kyprianou.Ch04.ito43_spatial_small_tail_grid_pathwise
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
    (T : NNReal) (hTH : T ≤ H) (n : ℕ) (t : NNReal) (ht : t ≤ T) :
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    let chi : ℝ → ℝ := fun z => min 1 (max 0 (|z| * ((m : ℝ) + 1) - 1))
    |(∑ k ∈ Finset.range n,
          (f ((v k : Real), X (v (k+1)) omega) -
          f ((v k : Real), X (v k) omega) -
          deriv (fun x : Real => f ((u k : Real), x)) (X (u k) omega) *
            (X (v (k+1)) omega - X (v k) omega))) - (∑ k ∈ Finset.range n,
      iteratedDeriv 2 (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * (X (v (k+1)) omega - X (v k) omega)^2 / 2) - (∑ k ∈ Finset.range n,
       let dx := X (v (k+1)) omega - X (v k) omega
       (f ((v k : ℝ),X (v (k+1)) omega) - f ((v k : ℝ),X (v k) omega) -
        deriv (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * dx -
        iteratedDeriv 2 (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * dx^2 / 2)
          * chi dx)| ≤
      a*∑ k ∈ Finset.range n, (X (v (k+1)) omega-X (v k) omega)^2 := by sorry
