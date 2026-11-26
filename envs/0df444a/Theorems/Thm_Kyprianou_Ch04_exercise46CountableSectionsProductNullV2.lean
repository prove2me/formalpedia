-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46CountableSectionsProductNullV2
-- name    : Kyprianou.Ch04.exercise46CountableSectionsProductNullV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T23:28:24.78598+00:00
-- url     : https://prove2.me/theorems/ae2d47d9-6a51-4318-9975-089f9a7c9cc3
-- title:
--   A measurable set with almost surely countable time sections has zero product measure
-- statement:
--   Use Tonelli on time sections, each countable section having zero atomless time measure.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46CountableSectionsProductNullV2
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (m : Measure NNReal) [SFinite m] [NullSingletonClass m]
    (S : Set (Omega × NNReal)) (hS : MeasurableSet S)
    (hCount : ∀ᵐ w ∂P, (Prod.mk w ⁻¹' S).Countable) :
    (P.prod m) S = 0 := by
  sorry
