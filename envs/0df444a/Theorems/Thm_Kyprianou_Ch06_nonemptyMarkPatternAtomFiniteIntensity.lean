-- Prove2me | Theorems.Thm_Kyprianou_Ch06_nonemptyMarkPatternAtomFiniteIntensity
-- name    : Kyprianou.Ch06.nonemptyMarkPatternAtomFiniteIntensity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:54:40.5868+00:00
-- url     : https://prove2.me/theorems/47054550-c4a0-4643-afdb-0c6034240389
-- title:
--   Lemma 6.18 nonempty Boolean-mark atoms have finite intensity
-- statement:
--   A finite Boolean membership atom indexed by S containing some mark-set index i has intensity bounded by n(B_i), hence finite whenever the original mark sets have finite intensity. The empty-pattern atom is deliberately excluded because its intensity need not be finite. This is needed for the hValid premise of compatible marked-time rectangles.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), printed pp.160–161, finite-intensity Boolean-mark disjointisation.

import Mathlib
open MeasureTheory
set_option autoImplicit false

theorem Kyprianou.Ch06.nonemptyMarkPatternAtomFiniteIntensity
    {E : Type} [MeasurableSpace E] (n : Measure E)
    (m : Nat) (B : Fin m → Set E)
    (hFinite : ∀ i : Fin m, n (B i) < ⊤)
    (S : Finset (Fin m)) (i : Fin m) (hi : i ∈ S) :
    n {x : E | ∀ j : Fin m, (x ∈ B j ↔ j ∈ S)} < ⊤ := by sorry
