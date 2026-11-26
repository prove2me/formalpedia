-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41FiniteLiminfV2
-- name    : Kyprianou.Ch04.exercise41FiniteLiminfV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:31:59.917883+00:00
-- url     : https://prove2.me/theorems/7834d3f1-3dcf-4a06-bf7c-599bac21c755
-- title:
--   Fatou bound implies almost surely finite lower limit
-- statement:
--   Fatou bound implies almost surely finite lower limit
-- source:
--   Kyprianou (2006), Chapter 4, Exercises 4.1 and 4.9.

import Mathlib

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41FiniteLiminfV2 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (N : ℕ → Ω → ℝ≥0∞) (C : ℝ≥0∞)
    (hC : C < ⊤) (hN : ∀ n, Measurable (N n))
    (hBound : ∀ n, (∫⁻ ω, N n ω ∂P) ≤ C) :
    ∀ᵐ ω ∂P, Filter.liminf (fun n => N n ω) atTop < ⊤  := by
  sorry
