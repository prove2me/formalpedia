-- Prove2me | Theorems.Thm_Kyprianou_Ch06_finiteBooleanMarkAtomsMeasurableDisjointCover
-- name    : Kyprianou.Ch06.finiteBooleanMarkAtomsMeasurableDisjointCover
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:52:48.984243+00:00
-- url     : https://prove2.me/theorems/d3860460-ef7a-453e-b294-f9e8635e64e7
-- title:
--   Lemma 6.18 Boolean mark atoms are measurable, disjoint and reconstruct the original mark sets
-- statement:
--   For any finite family of measurable mark sets B_i, the Boolean atom indexed by a membership pattern S ⊆ Fin m is measurable; distinct patterns give disjoint sets; and each B_i is exactly the union of those membership atoms whose patterns contain i. This is the fundamental spatial disjointisation needed to represent arbitrary overlapping outside-mark cylinders in Chapter 6 Lemma 6.18.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), printed pp.160–161, finite Boolean-mark partition in the proof of Poisson independence.

import Mathlib
set_option autoImplicit false

theorem Kyprianou.Ch06.finiteBooleanMarkAtomsMeasurableDisjointCover
    {E : Type} [MeasurableSpace E] (m : Nat)
    (B : Fin m → Set E) (hB : ∀ i, MeasurableSet (B i)) :
    (∀ S : Finset (Fin m),
      MeasurableSet {x : E | ∀ i : Fin m,
        (x ∈ B i ↔ i ∈ S)}) ∧
    (∀ S T : Finset (Fin m), S ≠ T →
      Disjoint
        {x : E | ∀ i : Fin m, (x ∈ B i ↔ i ∈ S)}
        {x : E | ∀ i : Fin m, (x ∈ B i ↔ i ∈ T)}) ∧
    (∀ (i : Fin m) (x : E), x ∈ B i ↔
      ∃ S : Finset (Fin m),
        (∀ j : Fin m, (x ∈ B j ↔ j ∈ S)) ∧ i ∈ S) := by sorry
