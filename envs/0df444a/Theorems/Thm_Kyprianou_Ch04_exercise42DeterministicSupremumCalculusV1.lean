-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42DeterministicSupremumCalculusV1
-- name    : Kyprianou.Ch04.exercise42DeterministicSupremumCalculusV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T08:23:08.549548+00:00
-- url     : https://prove2.me/theorems/4f929453-4ce9-42eb-885d-5765e84491a8
-- title:
--   Pathwise running-supremum BV chain rule with exact left-grid limit
-- statement:
--   Use the fixed continuous running supremum and finite jump truncations; integrate on the affine intervals and take absolutely dominated limits, independently identifying the Stieltjes left-point sums.
-- source:
--   Kyprianou (2006), Exercise 4.2, p. 106 and solution p. 317; deterministic and source-law reduction.

import Mathlib
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

theorem Kyprianou.Ch04.exercise42DeterministicSupremumCalculusV1
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
    (hPos : ∀ t : NNReal, 0 < t →
      0 < sSup ((fun s : NNReal => X s omega) '' Set.Iic t))
    (hMon : Monotone (fun t : NNReal => (t : Real) * c - X t omega))
    (f : Real × Real → Real)
    (hf : ContDiffOn Real 1 f (Set.prod (Set.Ici (0 : Real)) Set.univ)) :
    let supX : NNReal -> Omega -> Real := fun t omega =>
      sSup ((fun s : NNReal => X s omega) '' Set.Iic t)
    ∀ t : NNReal,
      ∃ maxIntegral : Real,
        Tendsto
          (fun n : Nat =>
            ∑ k ∈ Finset.range n,
              let u : NNReal := t * (k : NNReal) / (n : NNReal)
              let v : NNReal := t * ((k + 1 : Nat) : NNReal) / (n : NNReal)
              fderiv Real f (supX u omega, X u omega) (1, 0) *
                (supX v omega - supX u omega))
          atTop (nhds maxIntegral) ∧
        f (supX t omega, X t omega) =
          f (supX 0 omega, X 0 omega) +
          c *
            (∫ s in Set.Icc (0 : Real) (t : Real),
              fderiv Real f
                (supX (Real.toNNReal s) omega, X (Real.toNNReal s) omega)
                (0, 1) ∂volume) +
          maxIntegral +
          (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
              (Set.Iio (0 : Real)),
            (f (supX (Real.toNNReal z.1) omega,
                Xleft (Real.toNNReal z.1) omega + z.2) -
              f (supX (Real.toNNReal z.1) omega,
                Xleft (Real.toNNReal z.1) omega))
            ∂(pathJumpMeasure X Xleft omega)) := by
  sorry
