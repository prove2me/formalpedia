-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiLinearClockWitness
-- name    : Kyprianou.Ch01.reverseLampertiLinearClockWitness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T14:16:42.433879+00:00
-- url     : https://prove2.me/theorems/66a6ca05-8b36-400b-8037-af8179929e15
-- title:
--   Strict crossing time exists for the linear reciprocal occupation clock
-- statement:
--   If y*t<A for nonnegative initial state y, some physical time s<A has s/y>t in extended-nonnegative arithmetic, including y=0 with the inverse-speed convention.
-- source:
--   Kyprianou (2006), Section 1.3.4, first-arrival inverse-speed clock scaling.

import Mathlib.Data.ENNReal.Basic
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiLinearClockWitness
    (y : Nat) (t : NNReal) (A : Real)
    (hBefore : (y : Real) * (t : Real) < A) :
    ∃ s : NNReal, (s : Real) < A ∧
      (t : ENNReal) < (y : ENNReal)⁻¹ * (s : ENNReal) := by
  sorry
