-- Prove2me | Theorems.Thm_Kyprianou_Ch06_independentEventOfAeDisjointCountableUnion
-- name    : Kyprianou.Ch06.independentEventOfAeDisjointCountableUnion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:23:15.825446+00:00
-- url     : https://prove2.me/theorems/76203951-bbda-426f-979a-d039fada520b
-- title:
--   Event independence transfers through almost-sure equivalence to a disjoint countable union
-- statement:
--   If a measurable event D is independently factorised with each member of a pairwise disjoint countable measurable family F_i, and a second event G is almost surely equivalent to the union of the F_i, then P(D∩G)=P(D)P(G). The proof applies the independently Proved disjoint-union factorisation, and replaces each occurrence of the union event by G using the same probability-null exceptional set and measure_congr. This is the source-faithful measure-theoretic bridge needed to transfer Poisson disjoint spatial atom independence to overlapping-mark count cylinders.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.independentEventOfAeDisjointCountableUnion
    {Omega I : Type} [MeasurableSpace Omega] [Countable I]
    (P : Measure Omega) (D G : Set Omega)
    (hD : MeasurableSet D) (F : I → Set Omega)
    (hF : ∀ i, MeasurableSet (F i))
    (hPair : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hIndependent : ∀ i, P (D ∩ F i) = P D * P (F i))
    (hAe : ∀ᵐ omega ∂P, (omega ∈ G) ↔
      omega ∈ ⋃ i, F i) :
    P (D ∩ G) = P D * P G := by sorry
