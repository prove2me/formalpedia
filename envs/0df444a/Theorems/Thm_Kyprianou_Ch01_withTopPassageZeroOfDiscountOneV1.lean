-- Prove2me | Theorems.Thm_Kyprianou_Ch01_withTopPassageZeroOfDiscountOneV1
-- name    : Kyprianou.Ch01.withTopPassageZeroOfDiscountOneV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:28:50.307316+00:00
-- url     : https://prove2.me/theorems/d27aa168-de31-4c76-b13d-3885d22da36c
-- title:
--   Extended passage time with unit exponential discount must be zero
-- statement:
--   For a possibly infinite nonnegative passage time, unit discount exp(-T)=1 with the source convention exp(-infinity)=0 implies T=0. The infinite WithTop case contradicts 0=1. In a finite case use the pinned Real.exp_eq_one_iff to identify -(t:Real)=0, then NNReal coercion back to t=0.
-- source:
--   Kyprianou (2006), Chapter 1, extended first-passage discount and strict exponential monotonicity.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.withTopPassageZeroOfDiscountOneV1
    (T : WithTop ℝ≥0)
    (hOne : (match T with
      | none => (0 : ℝ)
      | some t => Real.exp (-(t : ℝ))) = 1) :
    T ≤ (0 : WithTop ℝ≥0) := by sorry
