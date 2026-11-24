-- Prove2me | Theorems.Thm_Kyprianou_Ch03_prod_expClock_discountMeasurableV1
-- name    : Kyprianou.Ch03.prod_expClock_discountMeasurableV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T16:46:00.639504+00:00
-- url     : https://prove2.me/theorems/dadf1479-5f82-44fd-8345-1a828cd5908a
-- title:
--   Measurable nonnegative exponential discount of an extended threshold
-- statement:
--   Measurability of the top event, measurable untopD, coercion to real, and continuous exponential.
-- source:
--   Kyprianou (2006), Exercise 3.6; faithful auxiliary reduction of e7615c25-61ff-4f34-bf1a-1f06850e5e0e.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.prod_expClock_discountMeasurableV1
    {Omega : Type} [MeasurableSpace Omega]
    (tau : Omega → WithTop NNReal) (htau : Measurable tau)
    (q : ℝ) :
    Measurable (fun w => if tau w = ⊤ then (0 : ℝ)
      else Real.exp (-q * (((tau w).untopD (0 : NNReal) : NNReal) : ℝ))) := by sorry
