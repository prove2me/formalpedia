-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_martingale_of_event_increment_zero
-- name    : Kyprianou.Ch04.kw48_martingale_of_event_increment_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:25:50.97734+00:00
-- url     : https://prove2.me/theorems/2138dfdd-35b3-55c2-a23a-4e7c4c0a6b83
-- title:
--   Complex martingale from signed increments on past events
-- statement:
--   Complex martingale from signed increments on past events.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i), complex product-grid proof.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.kw48_martingale_of_event_increment_zero
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (M : NNReal → Omega → Complex) (hAdapt : StronglyAdapted F M)
    (hInt : ∀ t, Integrable (M t) P)
    (hZero : ∀ a b : NNReal, a ≤ b → ∀ A : Set Omega, MeasurableSet[F a] A →
      (∫ w in A, (M a w - M b w) ∂P) = 0) :
    Martingale M F P  := by sorry
