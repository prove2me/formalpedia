-- Prove2me | Theorems.Thm_Kyprianou_Ch06_fourOverlapSpacetimeMarksDisjointFromA
-- name    : Kyprianou.Ch06.fourOverlapSpacetimeMarksDisjointFromA
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:37:06.321143+00:00
-- url     : https://prove2.me/theorems/16dd3d16-829b-44e2-b84d-68a1c5a676e0
-- title:
--   Four overlapping-mark spatial atoms are all disjoint from the first-arrival mark set A
-- statement:
--   Spatial subset monotonicity transfers original assumptions that A is disjoint from B and C to every one of the four time-split mark sets B\C, B∩C, C\B and C. No extra disjointness of B and C is assumed.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.fourOverlapSpacetimeMarksDisjointFromA
    {E : Type} [MeasurableSpace E]
    (A B C : Set E)
    (hAB : Disjoint A B) (hAC : Disjoint A C) :
    let marks : Fin 4 → Set E := fun i =>
      if i = 0 then B \ C else if i = 1 then B ∩ C
        else if i = 2 then C \ B else C
    ∀ i, Disjoint A (marks i) := by sorry
