-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteWeightedIndicatorIntegral
-- name    : Kyprianou.Ch04.finiteWeightedIndicatorIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:03:23.454586+00:00
-- url     : https://prove2.me/theorems/b93c3e67-d153-4018-97fb-071d26044cae
-- title:
--   Real integral of a finite weighted indicator sum
-- statement:
--   A finite sum of real weighted indicators of measurable finite-measure sets is integrable and its integral is the sum of the weights multiplied by the measures of their sets.
-- source:
--   Bochner integral of indicators; Kyprianou Chapter 4 Exercise 4.4 physical integral identification.

import Mathlib
open MeasureTheory
open scoped ENNReal BigOperators
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch04.finiteWeightedIndicatorIntegral
    {A : Type u} [MeasurableSpace A] {ι : Type v} [DecidableEq ι]
    (μ : Measure A) (s : Finset ι) (B : ι → Set A) (c : ι → ℝ)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFin : ∀ i ∈ s, μ (B i) ≠ ⊤) :
    Integrable (fun x => ∑ i ∈ s, (B i).indicator (fun _ => c i) x) μ ∧
      (∫ x, ∑ i ∈ s, (B i).indicator (fun _ => c i) x ∂μ) =
      ∑ i ∈ s, c i * (μ (B i)).toReal := by
  sorry
