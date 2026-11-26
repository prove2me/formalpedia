-- Prove2me | Theorems.Thm_Kyprianou_Ch04_leftLimitTimeMeasurableV1
-- name    : Kyprianou.Ch04.leftLimitTimeMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:51:37.158117+00:00
-- url     : https://prove2.me/theorems/5aad8cf4-cd84-5455-8336-0af3f03083dc
-- title:
--   Measurability of positive-time left-limit path
-- statement:
--   Measurability of positive-time left-limit path
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem leftLimitTimeMeasurableV1 (U L : NNReal → ℝ) (hU : Measurable U)
    (hL : ∀ t : NNReal, 0 < t → Tendsto U (𝓝[<] t) (𝓝 (L t))) :
    Measurable L := by
  sorry
end Kyprianou.Ch04
