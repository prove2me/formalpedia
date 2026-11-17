-- Prove2me | Theorems.Thm_Kyprianou_Ch06_threeMarkVennAtomsMeasurableFinite
-- name    : Kyprianou.Ch06.threeMarkVennAtomsMeasurableFinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:39:17.778196+00:00
-- url     : https://prove2.me/theorems/7517c962-426c-46f0-af27-1415c8e1af57
-- title:
--   Seven Venn atom mark regions preserve measurability and finite intensity
-- statement:
--   All seven nonempty three-mark Venn atoms are measurable subsets of one of the original finite-intensity measurable mark regions B,C,D. This supplies the exact source marked-Poisson rectangle law assumptions with no new restrictions on the original outside mark sets.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.threeMarkVennAtomsMeasurableFinite
    {E : Type} [MeasurableSpace E] (n : Measure E)
    (B C D : Set E) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hFB : n B < ⊤) (hFC : n C < ⊤) (hFD : n D < ⊤) :
    let marks : Fin 7 → Set E := fun i =>
      if i = 0 then (B \ C) \ D
      else if i = 1 then (C \ B) \ D
      else if i = 2 then (D \ B) \ C
      else if i = 3 then (B ∩ C) \ D
      else if i = 4 then (B ∩ D) \ C
      else if i = 5 then (C ∩ D) \ B
      else B ∩ C ∩ D
    ∀ i : Fin 7, MeasurableSet (marks i) ∧ n (marks i) < ⊤ := by sorry
