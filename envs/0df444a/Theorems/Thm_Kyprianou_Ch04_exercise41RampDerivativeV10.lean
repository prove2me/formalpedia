-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41RampDerivativeV10
-- name    : Kyprianou.Ch04.exercise41RampDerivativeV10
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:38:39.779018+00:00
-- url     : https://prove2.me/theorems/a9a1926f-fc06-5a1a-90c2-29b4527c4c07
-- title:
--   C1 primitive of a clipped linear ramp has the prescribed derivative and Lipschitz constant one
-- statement:
--   C1 primitive of a clipped linear ramp has the prescribed derivative and Lipschitz constant one
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), smooth approximation.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology Interval
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41RampDerivativeV10
    (ε : ℝ) (he : 0 < ε) :
    let r : ℝ → ℝ := fun x => min 1 (max 0 (x / ε))
    let p : ℝ → ℝ := fun x => ∫ u in (0 : ℝ)..x, r u
    ContDiff ℝ 1 p ∧ (∀ x, HasDerivAt p (r x) x) ∧
      LipschitzWith 1 p := by
  sorry
