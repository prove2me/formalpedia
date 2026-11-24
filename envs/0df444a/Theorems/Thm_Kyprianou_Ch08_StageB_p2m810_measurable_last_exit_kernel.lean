-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_measurable_last_exit_kernel
-- name    : Kyprianou.Ch08.StageB.p2m810_measurable_last_exit_kernel
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T19:40:04.790965+00:00
-- url     : https://prove2.me/theorems/66e82f62-4388-4656-99c6-4b22333b46a7
-- title:
--   Bounded jointly measurable discounted last-exit path kernel
-- statement:
--   There is a measurable bounded payoff on the product of starting position and future paths agreeing with the discounted last negative visit on right-continuous paths.
-- source:
--   Kyprianou (2006), Exercise 8.10(i),(iii)

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_measurable_last_exit_kernel
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ H : ℝ × (ℝ≥0 → ℝ) → ℝ,
      Measurable H ∧ (∀ z, 0 ≤ H z ∧ H z ≤ 1) ∧
      ∀ (x : ℝ) (f : ℝ≥0 → ℝ),
        (∀ t, ContinuousWithinAt f (Ici t) t) →
        H (x,f) = discountedAt q (lastNegativeVisit (fun t (_ : Unit) => x + f t) ()) := by
  sorry
