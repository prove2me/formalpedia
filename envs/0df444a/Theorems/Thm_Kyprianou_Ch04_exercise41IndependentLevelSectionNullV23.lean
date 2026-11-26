-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41IndependentLevelSectionNullV23
-- name    : Kyprianou.Ch04.exercise41IndependentLevelSectionNullV23
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:06:16.989623+00:00
-- url     : https://prove2.me/theorems/a74770e8-a001-4dfe-80c9-42c1e938fc62
-- title:
--   Independent level mixing preserves the null occupation property
-- statement:
--   Independent level mixing preserves the null occupation property
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41IndependentLevelSectionNullV23
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (X : ℝ × Ω → ℝ) (hX : Measurable X)
    (hOcc : ∀ᵐ w ∂P, ∀ b : ℝ, volume {s : ℝ | 0 ≤ s ∧ X (s,w) = b} = 0) :
    ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ p ∂P.prod μ,
      ¬ (0 ≤ s ∧ X (s,p.1) + p.2 = 0) := by
  sorry
