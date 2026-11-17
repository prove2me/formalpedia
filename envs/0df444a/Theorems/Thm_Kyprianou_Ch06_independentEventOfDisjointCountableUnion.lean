-- Prove2me | Theorems.Thm_Kyprianou_Ch06_independentEventOfDisjointCountableUnion
-- name    : Kyprianou.Ch06.independentEventOfDisjointCountableUnion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:12:33.263225+00:00
-- url     : https://prove2.me/theorems/f55d5861-80ac-416e-9c0c-cb436d53c538
-- title:
--   Independence of a measurable event from a countable disjoint union follows from independence of its pieces
-- statement:
--   If a measurable event D is independent, in the sense of exact probability factorisation, of each event in a countable measurable pairwise-disjoint family F_i, then D is independent of their union. This follows from disjoint countable additivity of the measure, distribution of multiplication over ENNReal sums and the given pointwise factorisations. The result is a reusable measure-theoretic bridge in the Chapter 6 marked-Poisson overlapping-count cylinder decomposition, without assuming the conclusion for non-disjoint families.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.independentEventOfDisjointCountableUnion
    {Omega I : Type} [MeasurableSpace Omega] [Countable I]
    (P : Measure Omega) (D : Set Omega)
    (hD : MeasurableSet D)
    (F : I → Set Omega)
    (hF : ∀ i, MeasurableSet (F i))
    (hPair : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hIndependent : ∀ i, P (D ∩ F i) = P D * P (F i)) :
    P (D ∩ ⋃ i, F i) = P D * P (⋃ i, F i) := by sorry
