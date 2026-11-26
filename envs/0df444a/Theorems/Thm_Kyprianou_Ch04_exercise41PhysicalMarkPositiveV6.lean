-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41PhysicalMarkPositiveV6
-- name    : Kyprianou.Ch04.exercise41PhysicalMarkPositiveV6
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:31:07.544423+00:00
-- url     : https://prove2.me/theorems/7e2b55a8-a9fe-43a7-a4fc-9aa0aeb6cd91
-- title:
--   Every actual nonzero marked jump in a measurable set contributes at least one to its physical count
-- statement:
--   Every actual nonzero marked jump in a measurable set contributes at least one to its physical count
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41PhysicalMarkPositiveV6
    (x : NNReal → ℝ) (l : NNReal → ℝ)
    (hx : Measurable x) (hl : Measurable l)
    (A : Set (NNReal × ℝ)) (hA : MeasurableSet A)
    (s : NNReal) (hs : 0 < s) (hj : x s - l s ≠ 0)
    (hm : (s, x s - l s) ∈ A) :
    1 ≤ ((Measure.count.restrict {u : NNReal | 0 < u ∧ x u - l u ≠ 0}).map
      (fun u => (u,x u - l u))) A  := by
  sorry
