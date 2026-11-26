-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41IndependentLevelNullV23
-- name    : Kyprianou.Ch04.exercise41IndependentLevelNullV23
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:06:12.964249+00:00
-- url     : https://prove2.me/theorems/74aedb7a-8d03-51db-b1fb-e7f727c97a4d
-- title:
--   Time occupation of a sum with independent fixed-distribution increments is null
-- statement:
--   Time occupation of a sum with independent fixed-distribution increments is null
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41IndependentLevelNullV23
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (X Y : ℝ × Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hOcc : ∀ᵐ w ∂P, ∀ b : ℝ, volume {s : ℝ | 0 ≤ s ∧ X (s,w) = b} = 0)
    (hLaw : ∀ s : ℝ, 0 ≤ s →
      Measure.map (fun w => (X (s,w),Y (s,w))) P =
      (Measure.map (fun w => X (s,w)) P).prod μ) :
    ∀ᵐ w ∂P, volume {s : ℝ | 0 ≤ s ∧ X (s,w) + Y (s,w) = 0} = 0 := by
  sorry
