-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableFracMomentNegativeTailWeightEqV1
-- name    : Kyprianou.Ch03.stableFracMomentNegativeTailWeightEqV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T16:18:45.616538+00:00
-- url     : https://prove2.me/theorems/825384a1-bfda-4be4-862c-b76234b50ba2
-- title:
--   Pointwise stable density weighted by an absolute power on the negative tail
-- statement:
--   On x≤−1, the density selects the negative-side coefficient, the nonnegative truncation is inert, and max(|x|,1)=−x. Use the positive-base real-power quotient identity.
-- source:
--   Kyprianou (2006), Exercise 3.3(iii); faithful auxiliary calculation for 77d888ef-0786-46e6-8087-f88dd6a186e1.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.stableFracMomentNegativeTailWeightEqV1
    (alpha cPlus cMinus eta x : Real) (hCMinus : 0 ≤ cMinus) (hx : x ≤ -1) :
    ((Real.toNNReal (if 0 < x then cPlus / (x ^ (1 + alpha))
       else if x < 0 then cMinus / ((-x) ^ (1 + alpha)) else 0) : NNReal) : Real) *
      (max |x| 1) ^ eta = cMinus * (-x) ^ (eta - 1 - alpha) := by sorry
