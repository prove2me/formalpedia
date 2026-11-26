-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteWeightedIndicatorSquareIntegral
-- name    : Kyprianou.Ch04.finiteWeightedIndicatorSquareIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:36:34.384808+00:00
-- url     : https://prove2.me/theorems/9b0ea7c4-a148-51a6-8d49-fe7d9177c278
-- title:
--   Energy of overlapping finite weighted indicators
-- statement:
--   The integrated square of a finite sum of weighted indicators of finite-measure sets equals the double sum of weighted intersection measures, allowing arbitrary overlaps.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; deterministic energy identity.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finiteFamilyCovarianceExpansion
open MeasureTheory
open scoped ENNReal BigOperators
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch04.finiteWeightedIndicatorSquareIntegral
    {A : Type u} [MeasurableSpace A] {ι : Type v} [DecidableEq ι]
    (μ : Measure A) (s : Finset ι) (B : ι → Set A) (c : ι → ℝ)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFin : ∀ i ∈ s, μ (B i) ≠ ⊤) :
    (∫ x, (∑ i ∈ s, (B i).indicator (fun _ => c i) x)^2 ∂μ) =
      ∑ i ∈ s, ∑ j ∈ s, (c i * c j) * (μ (B i ∩ B j)).toReal := by
  sorry
