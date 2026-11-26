-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_ucp_add
-- name    : Kyprianou.Ch04.ito43_ucp_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:45:38.604068+00:00
-- url     : https://prove2.me/theorems/c10eaf9a-1e79-595f-b0ae-d9328072ef89
-- title:
--   Uniform-in-probability errors combine by the union bound
-- statement:
--   Uniform-in-probability errors combine by the union bound.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Uniform-in-probability errors combine by the triangle inequality and union bound. -/

theorem Kyprianou.Ch04.ito43_ucp_add {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E G : ℕ → NNReal → Ω → ℝ) (T : NNReal)
    (hE : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => (P {w | ∃ t ≤ T, ε ≤ |E n t w|}).toReal) atTop (𝓝 0))
    (hG : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => (P {w | ∃ t ≤ T, ε ≤ |G n t w|}).toReal) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (P {w | ∃ t ≤ T, ε ≤ |E n t w + G n t w|}).toReal)
      atTop (𝓝 0) := by sorry
