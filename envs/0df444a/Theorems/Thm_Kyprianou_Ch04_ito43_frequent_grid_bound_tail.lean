-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_frequent_grid_bound_tail
-- name    : Kyprianou.Ch04.ito43_frequent_grid_bound_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:21:51.969244+00:00
-- url     : https://prove2.me/theorems/2e8a7edf-a3e7-59c1-bf68-8aff38023c2a
-- title:
--   Uniform upper tails bound failure of a frequent finite grid bound
-- statement:
--   Uniform upper tails bound failure of a frequent finite grid bound.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false

/-- An eventual uniform outer-probability tail bound bounds failure of a frequent grid bound. -/

theorem Kyprianou.Ch04.ito43_frequent_grid_bound_tail {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Q : ℕ → Ω → ℝ) (C η : ℝ) (hη : 0 ≤ η)
    (hQ : ∀ᶠ n in atTop, (P {w | C ≤ Q n w}).toReal ≤ η) :
    (P {w | ¬ ∃ᶠ n in atTop, Q n w < C}).toReal ≤ η := by sorry
