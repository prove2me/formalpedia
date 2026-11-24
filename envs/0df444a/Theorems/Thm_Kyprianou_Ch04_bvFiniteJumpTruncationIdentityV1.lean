-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpTruncationIdentityV1
-- name    : Kyprianou.Ch04.bvFiniteJumpTruncationIdentityV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T23:12:06.228656+00:00
-- url     : https://prove2.me/theorems/526f1a85-3971-458e-878c-fcd21c708b61
-- title:
--   Finite jump truncation: exact classical chain rule
-- statement:
--   For an arbitrary finite subset of actual jumps on the horizon, define the drift-plus-finite-jump path and its pre-jump values. Sort retained times, use the fundamental theorem of calculus on each affine segment, and telescope including endpoint jumps. No stochastic hypotheses enter.
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

theorem Kyprianou.Ch04.bvFiniteJumpTruncationIdentityV1
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
    let A : Finset (Set.Ioc (0 : NNReal) t) → Real :=
      fun S => f (0, X 0 omega) +
        (∫ u in Set.Icc (0 : Real) (t : Real),
          fderiv Real f (u, approx S (Real.toNNReal u)) (1, 0) ∂volume) +
        c * (∫ u in Set.Icc (0 : Real) (t : Real),
          fderiv Real f (u, approx S (Real.toNNReal u)) (0, 1) ∂volume) +
        ∑ s ∈ S, (f (((s : NNReal) : Real), approx S s) -
          f (((s : NNReal) : Real), before S s))
    ∀ S : Finset (Set.Ioc (0 : NNReal) t),
      f ((t : Real), approx S t) = A S := by
  sorry
