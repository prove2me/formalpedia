-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpTruncationLimitV1
-- name    : Kyprianou.Ch04.bvFiniteJumpTruncationLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:11:58.545486+00:00
-- url     : https://prove2.me/theorems/36c78a52-77d7-4caf-aa68-42dd7467d133
-- title:
--   Convergence of finite jump chain rule under absolute summability
-- statement:
--   Direct finite subsets by inclusion. Absolute summability gives uniform convergence of the truncated paths and their left limits. On a compact rectangle use continuity and boundedness of the partial derivatives away from time zero, dominated convergence for the time terms, and a uniform Lipschitz bound times each absolute jump for the series. The isolated boundary time zero is Lebesgue-null.
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

theorem Kyprianou.Ch04.bvFiniteJumpTruncationLimitV1
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
    Tendsto (fun S => f ((t : Real), approx S t)) atTop (nhds (f ((t : Real), X t omega))) ∧
    Tendsto A atTop (nhds (
                f (0, X 0 omega) +
        (∫ s in Set.Icc (0 : Real) (t : Real),
          fderiv Real f (s, X (Real.toNNReal s) omega)
            (1, 0) ∂volume) +
        c *
          (∫ s in Set.Icc (0 : Real) (t : Real),
            fderiv Real f (s, X (Real.toNNReal s) omega)
              (0, 1) ∂volume) +
        (∑' s : Set.Ioc (0 : NNReal) t,
          (f (((s : NNReal) : Real), X s omega) -
            f (((s : NNReal) : Real), Xleft s omega))))) := by
  sorry
