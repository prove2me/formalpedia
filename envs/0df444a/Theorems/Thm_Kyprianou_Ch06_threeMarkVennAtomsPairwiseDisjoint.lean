-- Prove2me | Theorems.Thm_Kyprianou_Ch06_threeMarkVennAtomsPairwiseDisjoint
-- name    : Kyprianou.Ch06.threeMarkVennAtomsPairwiseDisjoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:39:19.251393+00:00
-- url     : https://prove2.me/theorems/f8225872-fe7e-4ebf-a4b5-b8157c021573
-- title:
--   Seven nonempty Venn atom mark regions of three arbitrary sets are pairwise disjoint
-- statement:
--   The seven nonempty Boolean Venn atoms of three arbitrary sets B,C,D form a pairwise disjoint marked-space partition. This is the spatial compatibility certificate required by the original Chapter 6 marked-Poisson rectangle joint law for arbitrary three overlapping mark observations at the same time.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.threeMarkVennAtomsPairwiseDisjoint
    {E : Type} (B C D : Set E) :
    let marks : Fin 7 → Set E := fun i =>
      if i = 0 then (B \ C) \ D
      else if i = 1 then (C \ B) \ D
      else if i = 2 then (D \ B) \ C
      else if i = 3 then (B ∩ C) \ D
      else if i = 4 then (B ∩ D) \ C
      else if i = 5 then (C ∩ D) \ B
      else B ∩ C ∩ D
    ∀ i j : Fin 7, i ≠ j → Disjoint (marks i) (marks j) := by sorry
