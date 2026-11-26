-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteWeightedIndicatorExpectedSquareIntegral
-- name    : Kyprianou.Ch04.finiteWeightedIndicatorExpectedSquareIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:45:43.217547+00:00
-- url     : https://prove2.me/theorems/f05181ae-b836-4fe9-ad23-88c722296caf
-- title:
--   Expected energy of a finite weighted indicator sum
-- statement:
--   The expected squared intensity integral of a finite random-weighted indicator sum equals the sum of pairwise expected coefficient products multiplied by intersection measures, including overlapping sets.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; elementary predictable isometry.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finiteWeightedIndicatorSquareIntegral
import Theorems.Thm_Kyprianou_Ch04_integrableProductOfSquareIntegrable
open MeasureTheory
open scoped ENNReal BigOperators
set_option autoImplicit false
universe u v w

theorem Kyprianou.Ch04.finiteWeightedIndicatorExpectedSquareIntegral
    {Ω : Type u} {A : Type v} {ι : Type w}
    [MeasurableSpace Ω] [MeasurableSpace A] [DecidableEq ι]
    (P : Measure Ω) (μ : Measure A) (s : Finset ι)
    (B : ι → Set A) (H : ι → Ω → ℝ)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFin : ∀ i ∈ s, μ (B i) ≠ ⊤)
    (hHm : ∀ i ∈ s, AEStronglyMeasurable (H i) P)
    (hH2 : ∀ i ∈ s, Integrable (fun ω => (H i ω)^2) P) :
    (∫ ω, ∫ x, (∑ i ∈ s, (B i).indicator (fun _ => H i ω) x)^2 ∂μ ∂P) =
      ∑ i ∈ s, ∑ j ∈ s, (∫ ω, H i ω * H j ω ∂P) *
        (μ (B i ∩ B j)).toReal := by
  sorry
