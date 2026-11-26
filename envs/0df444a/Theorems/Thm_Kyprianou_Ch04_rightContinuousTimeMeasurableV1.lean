-- Prove2me | Theorems.Thm_Kyprianou_Ch04_rightContinuousTimeMeasurableV1
-- name    : Kyprianou.Ch04.rightContinuousTimeMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:51:41.575794+00:00
-- url     : https://prove2.me/theorems/9c99224c-b570-490a-8590-a00d14cd92b4
-- title:
--   Right continuous path is measurable in time
-- statement:
--   Right continuous path is measurable in time
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem rightContinuousTimeMeasurableV1 (U : NNReal → ℝ)
    (hU : ∀ t : NNReal, ContinuousWithinAt U (Ici t) t) : Measurable U := by
  sorry
end Kyprianou.Ch04
