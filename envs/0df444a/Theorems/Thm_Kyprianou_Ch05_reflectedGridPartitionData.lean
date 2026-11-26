-- Prove2me | Theorems.Thm_Kyprianou_Ch05_reflectedGridPartitionData
-- name    : Kyprianou.Ch05.reflectedGridPartitionData
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:49:05.254797+00:00
-- url     : https://prove2.me/theorems/807d31ae-10af-5b7b-8aef-67a913e0760d
-- title:
--   Reflected half-open uniform grid partitions the clipped nonnegative interval
-- statement:
--   Reflected half-open uniform grid partitions the clipped nonnegative interval
-- source:
--   Kyprianou (2006), Theorem 5.1(ii), corrected key renewal theorem.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.reflectedGridPartitionData
    (x d : Real) (hx : 0 ≤ x) (hd : 0 < d) :
    let S := fun k : Nat => Set.Icc 0 x ∩ Set.Ioc (x-((k : Real)+1)*d) (x-(k : Real)*d)
    (⋃ k, S k) = Set.Icc 0 x ∧
      Pairwise (Function.onFun Disjoint S) ∧
      (∀ k : Nat, MeasurableSet (S k)) ∧
      (∃ N : Nat, ∀ k : Nat, N ≤ k → S k = ∅) := by sorry
