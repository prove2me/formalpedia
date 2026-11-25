-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42GridCoefficientBoundV1
-- name    : Kyprianou.Ch04.exercise42GridCoefficientBoundV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T10:11:55.437276+00:00
-- url     : https://prove2.me/theorems/cf1fb665-5a04-56be-937f-3d7f1a3beb4c
-- title:
--   Compact bound for the sampled first partial derivative
-- statement:
--   Use milestone 1 compact path bounds and the continuous within-derivative on a compact rectangle; the full derivative either equals it or vanishes.
-- source:
--   Kyprianou (2006), Exercise 4.2; deterministic Stieltjes grid proof.

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42GridCoefficientBoundV1
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
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : NNReal, s ≤ t → ‖(fun s : NNReal => fderiv ℝ f (U s, X s omega) (1, 0)) s‖ ≤ C := by
  sorry
