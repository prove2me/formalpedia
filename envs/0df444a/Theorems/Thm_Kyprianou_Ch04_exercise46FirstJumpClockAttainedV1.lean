-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46FirstJumpClockAttainedV1
-- name    : Kyprianou.Ch04.exercise46FirstJumpClockAttainedV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:27:06.217837+00:00
-- url     : https://prove2.me/theorems/9fdd429f-9191-5628-a3b8-3e0b838a28a6
-- title:
--   First negative jump clock is the first attained jump time
-- statement:
--   An attained negative jump with a jump-free prefix is exactly the infimum of negative jump times.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46FirstJumpClockAttainedV1
    (f : NNReal → Real) (a : NNReal) (ha : 0 < a)
    (hJump : f a - Function.leftLim f a < 0)
    (hBefore : ∀ t : NNReal, 0 < t → t < a → f t = Function.leftLim f t) :
    (⨅ t : NNReal, if 0 < t ∧ f t - Function.leftLim f t < 0
      then (t : WithTop NNReal) else ⊤) = (a : WithTop NNReal) := by
  sorry
