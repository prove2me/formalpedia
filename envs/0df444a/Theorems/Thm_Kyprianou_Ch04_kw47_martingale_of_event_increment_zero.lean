-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_martingale_of_event_increment_zero
-- name    : Kyprianou.Ch04.kw47_martingale_of_event_increment_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T11:40:19.113899+00:00
-- url     : https://prove2.me/theorems/3e7a731b-3708-4548-a456-521a6400d01b
-- title:
--   Martingale from adapted integrable process with centred increments
-- statement:
--   Equality of conditional expectation follows from equality of event integrals of the earlier and later process values and strong adaptation.
-- source:
--   Kyprianou (2006), Exercise 4.7; deterministic product-grid martingale transfer.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_martingale_of_event_increment_zero
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (M : NNReal → Omega → Real) (hAdapt : StronglyAdapted F M)
    (hInt : ∀ t, Integrable (M t) P)
    (hZero : ∀ a b : NNReal, a ≤ b → ∀ A : Set Omega, MeasurableSet[F a] A →
      (∫ w in A, (M a w - M b w) ∂P) = 0) :
    Martingale M F P := by sorry
