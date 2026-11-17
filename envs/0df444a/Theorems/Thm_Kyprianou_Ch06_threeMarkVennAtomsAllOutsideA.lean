-- Prove2me | Theorems.Thm_Kyprianou_Ch06_threeMarkVennAtomsAllOutsideA
-- name    : Kyprianou.Ch06.threeMarkVennAtomsAllOutsideA
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:39:20.84829+00:00
-- url     : https://prove2.me/theorems/56218e12-d41b-474c-8172-b71d87a73ad8
-- title:
--   Seven Venn atom regions of three outside mark sets all remain outside A
-- statement:
--   Given the original Chapter 6 assumptions that A is disjoint from each of B,C,D, all seven Boolean Venn cells are disjoint from A. This is the external spatial separation certificate enabling independent A zero-count and arbitrary three-overlap mark rectangle counts.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.threeMarkVennAtomsAllOutsideA
    {E : Type} (A B C D : Set E)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hAD : Disjoint A D) :
    let marks : Fin 7 → Set E := fun i =>
      if i = 0 then (B \ C) \ D
      else if i = 1 then (C \ B) \ D
      else if i = 2 then (D \ B) \ C
      else if i = 3 then (B ∩ C) \ D
      else if i = 4 then (B ∩ D) \ C
      else if i = 5 then (C ∩ D) \ B
      else B ∩ C ∩ D
    ∀ i : Fin 7, Disjoint A (marks i) := by sorry
