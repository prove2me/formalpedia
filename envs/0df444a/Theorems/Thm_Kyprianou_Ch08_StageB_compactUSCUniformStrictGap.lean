-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_compactUSCUniformStrictGap
-- name    : Kyprianou.Ch08.StageB.compactUSCUniformStrictGap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:38:20.259924+00:00
-- url     : https://prove2.me/theorems/9c4ad4bd-888c-49cc-b086-202778e36dd5
-- title:
--   Lemma 8.2: upper semicontinuity on a finite nonnegative compact interval turns pointwise strict bounds into a common reciprocal-integer margin
-- statement:
--   For a real-valued upper semicontinuous function on the compact interval from zero to a finite nonnegative time, a strict upper bound at every time of the interval implies a uniform upper bound below the same height by 1/(n+1) for some natural n. The maximum is attained on the compact interval and must lie strictly below the bound. Choose n by the Archimedean reciprocal lemma. This is the deterministic step that makes strict actual excursion-height events countably separable without assuming atomlessness.
-- source:
--   Pinned Mathlib UpperSemicontinuousOn.exists_isMaxOn, isCompact_Icc and exists_nat_one_div_lt; analytic child of stoppedStrictPathIffRationalMarginAE 582debc4-35af-4163-8545-1b9244cd563d in Chapter 8 Lemma 8.2.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.compactUSCUniformStrictGap
    (f : ℝ≥0 → ℝ) (a : ℝ≥0) (h : ℝ)
    (hUSC : UpperSemicontinuousOn f (Set.Icc 0 a))
    (hStrict : ∀ t : ℝ≥0, t ≤ a → f t < h) :
    ∃ n : ℕ, ∀ t : ℝ≥0, t ≤ a →
      f t < h - 1 / (((n + 1 : ℕ) : ℝ)) := by
  sorry
