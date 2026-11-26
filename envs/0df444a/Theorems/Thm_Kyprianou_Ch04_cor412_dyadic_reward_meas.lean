-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_dyadic_reward_meas
-- name    : Kyprianou.Ch04.cor412_dyadic_reward_meas
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:11:55.350158+00:00
-- url     : https://prove2.me/theorems/e7886b47-24b7-4efc-a04f-ff3556b8e2fb
-- title:
--   Countable dyadic infimum exponential path functional is measurable
-- statement:
--   Countable dyadic infimum exponential path functional is measurable.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The infimum of exponential path evaluations on the countable dyadic grid is measurable. -/

theorem Kyprianou.Ch04.cor412_dyadic_reward_meas (β : ℝ) :
    Measurable (fun f : NNReal → ℝ =>
      ⨅ q : ℕ × ℕ, ENNReal.ofReal (Real.exp (β * f ((q.1 : NNReal) / 2 ^ q.2)))) := by sorry
