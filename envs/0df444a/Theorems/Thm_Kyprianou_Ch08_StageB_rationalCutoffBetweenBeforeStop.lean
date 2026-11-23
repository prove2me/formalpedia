-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_rationalCutoffBetweenBeforeStop
-- name    : Kyprianou.Ch08.StageB.rationalCutoffBetweenBeforeStop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:50:54.152122+00:00
-- url     : https://prove2.me/theorems/25dbb40b-ee6e-4d9e-8b8d-622628401ab5
-- title:
--   Lemma 8.2: a rational clock lies strictly between any finite time and a later finite or infinite stopping clock
-- statement:
--   Given any finite nonnegative real time t strictly before an extended nonnegative time T, including T equal to infinity, there exists a nonnegative rational q whose nonnegative real image lies strictly between t and T. For finite T this follows from density of rationals in a nonempty interval; for infinite T take a rational between t and t+1. This supplies the safe real-to-rational cutoff needed to prove that the strict stopped-height condition holds at all real times.
-- source:
--   Pinned Mathlib exists_rat_btwn, Real.coe_toNNReal, WithTop.coe_lt_coe and WithTop.ne_top_iff_exists; child of linked Chapter 8 Lemma 8.2 rightContinuousStoppedRationalMarginImpliesStrict b39a75fc-d0fe-48fc-af01-1d535ea157d3.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.rationalCutoffBetweenBeforeStop
    (t : ℝ≥0) (T : WithTop ℝ≥0)
    (ht : (t : WithTop ℝ≥0) < T) :
    ∃ q : ℚ, 0 ≤ q ∧
      t < (q : ℝ).toNNReal ∧
      ((q : ℝ).toNNReal : WithTop ℝ≥0) < T := by
  sorry
