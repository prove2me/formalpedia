-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41ClockUpperV13
-- name    : Kyprianou.Ch04.exercise41ClockUpperV13
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:57:49.219876+00:00
-- url     : https://prove2.me/theorems/af421518-55c5-4ca2-a65b-917b9efd59f3
-- title:
--   Dense near-zero clocks have upper bound at a zero visit
-- statement:
--   Dense near-zero clocks have upper bound at a zero visit
-- source:
--   Kyprianou (2006), Exercise 4.1(ii) auxiliary result

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41ClockUpperV13
    (x : NNReal → ℝ) (q : ℕ → NNReal) (hq : DenseRange q)
    (a s : NNReal) (has : a ≤ s)
    (hr : ContinuousWithinAt x (Ici s) s) (hz : x s = 0) :
    (⨆ n : ℕ, ⨅ k : ℕ, if a ≤ q k ∧ |x (q k)| < 1 / ((n : ℝ) + 1)
      then (q k : WithTop NNReal) else ⊤) ≤ (s : WithTop NNReal) := by
  sorry
