-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41FiniteTelescopingV7
-- name    : Kyprianou.Ch04.exercise41FiniteTelescopingV7
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:14:35.541439+00:00
-- url     : https://prove2.me/theorems/6535d14d-ee18-5688-a747-e2f8e748ad5d
-- title:
--   Finite ordered ledger telescoping
-- statement:
--   Finite ordered ledger telescoping
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41FiniteTelescopingV7
    (n : ℕ) (v : ℕ → ℝ) :
    (∑ k ∈ Finset.range n, (v (k + 1) - v k)) = v n - v 0 := by
  sorry
