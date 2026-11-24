-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableFracMomentPositiveTailWeightedV1
-- name    : Kyprianou.Ch03.stableFracMomentPositiveTailWeightedV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T16:02:35.16718+00:00
-- url     : https://prove2.me/theorems/8abbdc04-43ef-4c58-afe2-ff8d09f9110b
-- title:
--   Positive stable tail weighted-density equivalence
-- statement:
--   Restrict the density to the positive tail, transfer integration against the density to integration of the weighted function against volume, then simplify pointwise using positive real powers.
-- source:
--   Kyprianou (2006), Exercise 3.3(iii), decomposition of f3327e25-b159-4162-a83e-a9e9ea54926b.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.stableFracMomentPositiveTailWeightedV1
    (alpha cPlus cMinus eta : Real) (hCPlus : 0 ≤ cPlus)
    (hCMinus : 0 ≤ cMinus) (hEta : 0 < eta) :
    IntegrableOn (fun x : Real => (max |x| 1) ^ eta) (Set.Ici (1 : Real))
      ((volume : Measure Real).withDensity
        (fun x : Real => ENNReal.ofReal
          (if 0 < x then cPlus / (x ^ (1 + alpha))
           else if x < 0 then cMinus / ((-x) ^ (1 + alpha))
           else 0))) ↔
    IntegrableOn (fun x : Real => cPlus * x ^ (eta - 1 - alpha))
      (Set.Ici (1 : Real)) volume := by sorry
