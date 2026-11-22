-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_exp_clock_bracket_section
-- name    : Kyprianou.Ch08.StageB.source_result81_exp_clock_bracket_section
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:17:53.340709+00:00
-- url     : https://prove2.me/theorems/2f55f412-48f9-4222-b951-4ad9a12fad3b
-- title:
--   Exponential law of a bracketed passage event
-- statement:
--   An event between the strict and weak upper tails of a passage clock has exponential probability equal to the discounted passage value. The exponential measure has no atoms and the time is positive almost surely. Infinite passage time yields the empty event.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1, identity (8.6). Mathematical reduction of 80e7c39b-072e-47d5-a5d3-7fe26d044dc0.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.Distributions.Exponential
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_exp_clock_bracket_section
    (q : ℝ) (hq : 0 < q) (τ : WithTop ℝ≥0) (E : Set ℝ)
    (hE : ∀ r : ℝ,
      (τ < (r.toNNReal : WithTop ℝ≥0) → r ∈ E) ∧
      (r ∈ E → τ ≤ (r.toNNReal : WithTop ℝ≥0))) :
    (expMeasure q).real E = discountedAt q τ := by
  sorry
