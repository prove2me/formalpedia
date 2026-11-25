-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49PositiveDriftAlmostSurePositivePersistenceV1
-- name    : Kyprianou.Ch04.exercise49PositiveDriftAlmostSurePositivePersistenceV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T18:44:45.616911+00:00
-- url     : https://prove2.me/theorems/4458b34d-9028-4678-9198-49fd16e5b818
-- title:
--   Almost-sure positive small-time drift gives positive downward-persistence probability
-- statement:
--   For any probability space, if X_t/t converges almost surely to a strictly positive drift, then the first passage time below zero is strictly positive with positive probability (indeed almost surely). This does not require measurability of the first passage event beyond outer-measure monotonicity.
-- source:
--   Deterministic probability reduction for Kyprianou (2006), Exercise 4.9(ii), printed page 109.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49PositiveDriftNoImmediateDowncrossingV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49PositiveDriftAlmostSurePositivePersistenceV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (d : ℝ) (hd : 0 < d)
    (h : ∀ᵐ ω ∂P, Tendsto (fun t : NNReal => X t ω / (t : ℝ))
      (nhdsWithin (0 : NNReal) (Ioi 0)) (nhds d)) :
    let τ : Ω → WithTop NNReal :=
      fun ω => sInf {u : WithTop NNReal |
        ∃ t : NNReal, u = ↑t ∧ 0 < t ∧ X t ω < 0}
    0 < P {ω : Ω | 0 < τ ω} := by
  sorry
