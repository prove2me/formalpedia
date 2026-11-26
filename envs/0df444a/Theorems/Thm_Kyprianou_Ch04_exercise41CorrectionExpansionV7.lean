-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41CorrectionExpansionV7
-- name    : Kyprianou.Ch04.exercise41CorrectionExpansionV7
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:17:09.123346+00:00
-- url     : https://prove2.me/theorems/d0bc65e3-2226-4bad-8ec1-1c48e7ed287e
-- title:
--   Expand the weighted arrival and departure counts without losing terminal or initial corrections
-- statement:
--   Expand the weighted arrival and departure counts without losing terminal or initial corrections
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41CorrectionExpansionV7
    (α β : ℝ) (l : NNReal → ℝ) (t : NNReal) (Z : Finset NNReal) :
    α * (∑ s ∈ Z, if l s = 0 then (1 : ℝ) else 0) +
      β * ((if 0 < t then 1 else 0) + ∑ s ∈ Z, if s < t then 1 else 0) =
      (if 0 < t then β else 0) +
      ∑ s ∈ Z, ((if l s = 0 then α else 0) + (if s < t then β else 0)) := by
  sorry
