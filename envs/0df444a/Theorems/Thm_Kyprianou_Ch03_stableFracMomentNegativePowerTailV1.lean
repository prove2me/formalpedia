-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableFracMomentNegativePowerTailV1
-- name    : Kyprianou.Ch03.stableFracMomentNegativePowerTailV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T16:02:34.153835+00:00
-- url     : https://prove2.me/theorems/a370a94d-855e-4387-a277-9bd4e4f22e4e
-- title:
--   Negative real-power tail integral criterion
-- statement:
--   Use the reflection invariance of Lebesgue measure to reduce the negative tail to the positive tail.
-- source:
--   Kyprianou (2006), Exercise 3.3(iii), decomposition of f3327e25-b159-4162-a83e-a9e9ea54926b.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.stableFracMomentNegativePowerTailV1
    (c alpha eta : Real) :
    IntegrableOn (fun x : Real => c * (-x) ^ (eta - 1 - alpha))
      (Set.Iic (-1 : Real)) volume ↔ c = 0 ∨ eta < alpha := by sorry
