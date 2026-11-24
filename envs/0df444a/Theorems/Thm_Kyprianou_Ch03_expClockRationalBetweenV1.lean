-- Prove2me | Theorems.Thm_Kyprianou_Ch03_expClockRationalBetweenV1
-- name    : Kyprianou.Ch03.expClockRationalBetweenV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T16:46:01.122503+00:00
-- url     : https://prove2.me/theorems/e223628d-945a-4b97-b627-3f6c33352c27
-- title:
--   Rational separator of an extended nonnegative threshold and a finite clock
-- statement:
--   Use density of finite NNReal in WithTop and rational density in NNReal.
-- source:
--   Kyprianou (2006), Exercise 3.6; faithful auxiliary reduction of e7615c25-61ff-4f34-bf1a-1f06850e5e0e.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.expClockRationalBetweenV1
    (a : WithTop NNReal) (b : NNReal) :
    a < (b : WithTop NNReal) ↔
      ∃ r : ℚ, a < ((r : ℝ).toNNReal : WithTop NNReal) ∧
        (r : ℝ).toNNReal < b := by sorry
