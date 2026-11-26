-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41LeftZeroCountableV6
-- name    : Kyprianou.Ch04.exercise41LeftZeroCountableV6
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:22:22.189797+00:00
-- url     : https://prove2.me/theorems/7426cc36-f43d-5116-a727-c8b36672e040
-- title:
--   Left-limit zero set on a compact horizon is countable if actual zero visits are locally finite
-- statement:
--   Left-limit zero set on a compact horizon is countable if actual zero visits are locally finite
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41LeftZeroCountableV6
    (x : NNReal → ℝ) (T : NNReal)
    (hR : ∀ t : NNReal, ContinuousWithinAt x (Ici t) t)
    (hL : ∀ t : NNReal, 0 < t → ∃ l : ℝ,
      Tendsto x (nhdsWithin t (Iio t)) (nhds l))
    (hZ : Set.Finite {s : NNReal | 0 < s ∧ s ≤ T ∧ x s = 0}) :
    Set.Countable {s : NNReal | 0 < s ∧ s ≤ T ∧ Function.leftLim x s = 0}  := by
  sorry
