-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableFracMomentPositivePowerTailV1
-- name    : Kyprianou.Ch03.stableFracMomentPositivePowerTailV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T16:02:33.369199+00:00
-- url     : https://prove2.me/theorems/2ff3c317-837b-4de5-8598-4839741346bb
-- title:
--   Positive real-power tail integral criterion
-- statement:
--   For c=0 use the zero integrand; otherwise cancel the nonzero constant and use the exact real-power integral criterion on the open half-line.
-- source:
--   Kyprianou (2006), Exercise 3.3(iii), decomposition of f3327e25-b159-4162-a83e-a9e9ea54926b.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.stableFracMomentPositivePowerTailV1
    (c alpha eta : Real) :
    IntegrableOn (fun x : Real => c * x ^ (eta - 1 - alpha))
      (Set.Ici (1 : Real)) volume ↔ c = 0 ∨ eta < alpha := by sorry
