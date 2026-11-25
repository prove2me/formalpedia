-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvTruncationJumpLedgerLimitV1
-- name    : Kyprianou.Ch04.bvTruncationJumpLedgerLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:33:03.163328+00:00
-- url     : https://prove2.me/theorems/b63a88a7-9a61-4144-a8b4-aebb0163ba78
-- title:
--   BV finite actual-jump truncation: nonlinear jump ledger convergence
-- statement:
--   Uniform absolute-tail estimates control the approximating paths and left limits. On the fixed compact spatial range the mean-value bound controls every retained jump increment by C times its actual absolute jump, also controlling the limiting increments. For a finite core use pointwise convergence and for the complement use summability of the majorant, without assuming the indexing filter is countably generated.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.2, p. 91; deterministic pathwise auxiliary obligation.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

theorem Kyprianou.Ch04.bvTruncationJumpLedgerLimitV1
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega) (c : Real)
    (hCadlag : IsCadlag (fun t : NNReal => X t omega))
    (hLeft : forall t : NNReal, 0 < t →
      Tendsto (fun s : NNReal => X s omega)
        (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
    (hRep : forall t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|) ∧
      X t omega = X 0 omega + c * (t : Real) +
        ∑' s : Set.Ioc (0 : NNReal) t, (X s omega - Xleft s omega))
    (f : Real × Real → Real)
    (hf : ContDiffOn Real 1 f (Set.prod (Set.Ici (0 : Real)) Set.univ))
    (t : NNReal) :
    let jump : Set.Ioc (0 : NNReal) t → Real :=
      fun s => X s omega - Xleft s omega
    let approx : Finset (Set.Ioc (0 : NNReal) t) → NNReal → Real :=
      fun S u => X 0 omega + c * (u : Real) +
        ∑ s ∈ S, if (s : NNReal) ≤ u then jump s else 0
    let before : Finset (Set.Ioc (0 : NNReal) t) → NNReal → Real :=
      fun S u => X 0 omega + c * (u : Real) +
        ∑ s ∈ S, if (s : NNReal) < u then jump s else 0
    Tendsto (fun S : Finset (Set.Ioc (0 : NNReal) t) => ∑ s ∈ S, (f (((s : NNReal) : Real), approx S s) -
      f (((s : NNReal) : Real), before S s))) atTop
      (nhds (∑' s : Set.Ioc (0 : NNReal) t,
        (f (((s : NNReal) : Real), X s omega) -
          f (((s : NNReal) : Real), Xleft s omega)))) := by
  sorry
