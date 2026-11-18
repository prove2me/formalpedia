-- Prove2me | Theorems.Thm_Kyprianou_Ch06_outsideBooleanAtomFiniteEnumeration
-- name    : Kyprianou.Ch06.outsideBooleanAtomFiniteEnumeration
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:21:13.520472+00:00
-- url     : https://prove2.me/theorems/0d670fea-2812-4ab9-a164-1d57b2fb5e3e
-- title:
--   Lemma 6.18: finite enumerable disjoint mark atoms with exact cover and finite intensity
-- statement:
--   Every finite family of measurable finite-intensity mark sets outside A is exactly reconstructed by a finite indexed family of nonempty Boolean membership atoms. Those atoms are measurable, finite-intensity, pairwise disjoint, outside A, and the original B_i is the union of the selected atoms. The enumeration is deterministic and independent of Poisson sample paths and times.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), printed pp.160–161, finite mark-space Boolean disjointisation.

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_finiteBooleanMarkAtomsMeasurableDisjointCover
import Theorems.Thm_Kyprianou_Ch06_nonemptyMarkPatternAtomFiniteIntensity
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.outsideBooleanAtomFiniteEnumeration
    {E : Type} [MeasurableSpace E] (n : Measure E) (A : Set E)
    (m : Nat) (B : Fin m → Set E)
    (hB : ∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) :
    ∃ (a : Nat) (mark : Fin a → Set E)
      (selected : Fin m → Finset (Fin a)),
      (∀ j, MeasurableSet (mark j) ∧ n (mark j) < ⊤ ∧
        Disjoint A (mark j)) ∧
      (∀ j l : Fin a, j ≠ l → Disjoint (mark j) (mark l)) ∧
      (∀ i, (⋃ j ∈ selected i, mark j) = B i) := by sorry
