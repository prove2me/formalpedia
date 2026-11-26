-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41IncreasingCountLimitV4
-- name    : Kyprianou.Ch04.exercise41IncreasingCountLimitV4
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:23:19.517832+00:00
-- url     : https://prove2.me/theorems/f3594fea-8455-5cd7-81cb-4e8e7de41bfb
-- title:
--   Increasing finite grid counts have a measurable uniformly bounded supremum
-- statement:
--   Increasing finite grid counts have a measurable uniformly bounded supremum
-- source:
--   Kyprianou (2006), Exercise 4.1(i).

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41IncreasingCountLimitV4
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (I : Finset ℕ) (A : ℕ → ℕ → Set Ω) (C : ℝ≥0∞)
    (hm : ∀ m i, i ∈ I → MeasurableSet (A m i))
    (hmono : ∀ i ∈ I, Monotone (fun m => A m i))
    (hbound : ∀ m, ∑ i ∈ I, P (A m i) ≤ C) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ⨆ m : ℕ, ∑ i ∈ I, (A m i).indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω
    Measurable N ∧ (∫⁻ ω, N ω ∂P) ≤ C  := by
  sorry
