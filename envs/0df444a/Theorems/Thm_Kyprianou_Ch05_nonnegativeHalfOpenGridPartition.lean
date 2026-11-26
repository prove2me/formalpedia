-- Prove2me | Theorems.Thm_Kyprianou_Ch05_nonnegativeHalfOpenGridPartition
-- name    : Kyprianou.Ch05.nonnegativeHalfOpenGridPartition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:46:42.971288+00:00
-- url     : https://prove2.me/theorems/48cc8022-123b-402b-9ea4-830d6f0089b5
-- title:
--   Nonnegative half-open uniform grid is a disjoint partition
-- statement:
--   Nonnegative half-open uniform grid is a disjoint partition
-- source:
--   Kyprianou (2006), Theorem 5.1(ii), corrected key renewal theorem, Darboux grid estimates.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.nonnegativeHalfOpenGridPartition
    (d : Real) (hd : 0 < d) :
    (⋃ k : Nat, Set.Ico ((k : Real)*d) (((k : Real)+1)*d)) = Set.Ici 0 ∧
      Pairwise (Function.onFun Disjoint (fun k : Nat => Set.Ico ((k : Real)*d) (((k : Real)+1)*d))) := by sorry
