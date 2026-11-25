-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvTruncationDerivativeIntegralLimitV1
-- name    : Kyprianou.Ch04.bvTruncationDerivativeIntegralLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:28:35.060038+00:00
-- url     : https://prove2.me/theorems/d4703554-9a2c-4036-b187-76a1845d6f04
-- title:
--   BV finite actual-jump truncation: derivative integral convergence
-- statement:
--   Use absolute jump summability and horizon subtype reindexing to obtain uniform convergence of paths. All paths lie in a fixed compact rectangle. The continuous derivative within the half-plane agrees with the ordinary derivative for positive times; time zero has volume zero. Its uniform continuity gives uniform error on the positive-time rectangle and hence convergence of the finite-volume integrals for arbitrary directed finite subsets.
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

theorem Kyprianou.Ch04.bvTruncationDerivativeIntegralLimitV1
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
    (t : NNReal) (v : Real × Real) :
    let jump : Set.Ioc (0 : NNReal) t → Real :=
      fun s => X s omega - Xleft s omega
    let approx : Finset (Set.Ioc (0 : NNReal) t) → NNReal → Real :=
      fun S u => X 0 omega + c * (u : Real) +
        ∑ s ∈ S, if (s : NNReal) ≤ u then jump s else 0
    Tendsto (fun S => ∫ u in Set.Icc (0 : Real) (t : Real),
      fderiv Real f (u, approx S (Real.toNNReal u)) v ∂volume)
      atTop (nhds (∫ u in Set.Icc (0 : Real) (t : Real),
        fderiv Real f (u, X (Real.toNNReal u) omega) v ∂volume)) := by
  sorry
