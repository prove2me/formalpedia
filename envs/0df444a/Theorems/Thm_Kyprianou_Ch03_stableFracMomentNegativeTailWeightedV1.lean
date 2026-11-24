-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableFracMomentNegativeTailWeightedV1
-- name    : Kyprianou.Ch03.stableFracMomentNegativeTailWeightedV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T16:02:30.756977+00:00
-- url     : https://prove2.me/theorems/77d888ef-0786-46e6-8087-f88dd6a186e1
-- title:
--   Negative stable tail weighted-density equivalence
-- statement:
--   Restrict the density to the negative tail and use the same weighted-density transformation, with the positive variable -x.
-- source:
--   Kyprianou (2006), Exercise 3.3(iii), decomposition of f3327e25-b159-4162-a83e-a9e9ea54926b.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.stableFracMomentNegativeTailWeightedV1
    (alpha cPlus cMinus eta : Real) (hCPlus : 0 ≤ cPlus)
    (hCMinus : 0 ≤ cMinus) (hEta : 0 < eta) :
    IntegrableOn (fun x : Real => (max |x| 1) ^ eta) (Set.Iic (-1 : Real))
      ((volume : Measure Real).withDensity
        (fun x : Real => ENNReal.ofReal
          (if 0 < x then cPlus / (x ^ (1 + alpha))
           else if x < 0 then cMinus / ((-x) ^ (1 + alpha))
           else 0))) ↔
    IntegrableOn (fun x : Real => cMinus * (-x) ^ (eta - 1 - alpha))
      (Set.Iic (-1 : Real)) volume := by sorry
