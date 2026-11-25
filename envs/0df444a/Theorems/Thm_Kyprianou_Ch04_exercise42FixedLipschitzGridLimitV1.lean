-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42FixedLipschitzGridLimitV1
-- name    : Kyprianou.Ch04.exercise42FixedLipschitzGridLimitV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T08:33:04.298919+00:00
-- url     : https://prove2.me/theorems/0e270c5a-edff-5ed7-8c08-c9f957d9aaa8
-- title:
--   Left-grid Stieltjes sums converge for the fixed Lipschitz coordinate
-- statement:
--   Represent each Lipschitz increment as the integral of its derivative; grid left-endpoint values converge almost everywhere by cadlag continuity outside the countable discontinuity set, and compact bounds give dominated convergence.
-- source:
--   Kyprianou (2006), Exercise 4.2, p. 106 and solution p. 317; deterministic auxiliary or source-law bridge.

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open ProbabilityTheory Set Topology
open scoped Topology
open Kyprianou.Ch04

theorem Kyprianou.Ch04.exercise42FixedLipschitzGridLimitV1
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega) (c : Real)
    (hd : 0 < c) (hzero : X 0 omega = 0)
    (hCadlag : IsCadlag (fun t : NNReal => X t omega))
    (hLeft : ∀ t : NNReal, 0 < t →
      Tendsto (fun s : NNReal => X s omega)
        (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
    (hNeg : ∀ t : NNReal, 0 < t → X t omega ≤ Xleft t omega)
    (hRep : ∀ t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|) ∧
      X t omega = X 0 omega + c * (t : Real) +
        ∑' s : Set.Ioc (0 : NNReal) t, (X s omega - Xleft s omega))
    (U : NNReal → Real) (K : NNReal) (hU : LipschitzWith K U)
    (hU0 : 0 ≤ U 0) (hUp : ∀ s : NNReal, 0 < s → 0 < U s)
    (f : Real × Real → Real)
    (hf : ContDiffOn Real 1 f (Set.prod (Set.Ici (0 : Real)) Set.univ))
    (t : NNReal) :
    Tendsto (fun n : Nat => ∑ k ∈ Finset.range n,
        let u : NNReal := t * (k : NNReal) / (n : NNReal)
        let v : NNReal := t * ((k + 1 : Nat) : NNReal) / (n : NNReal)
        fderiv Real f (U u, X u omega) (1, 0) * (U v - U u))
      atTop (nhds (∫ s in Set.Icc (0 : Real) (t : Real),
        fderiv Real f (U s.toNNReal, X s.toNNReal omega) (1, 0) *
          deriv (fun z : Real => U z.toNNReal) s ∂volume)) := by
  sorry
