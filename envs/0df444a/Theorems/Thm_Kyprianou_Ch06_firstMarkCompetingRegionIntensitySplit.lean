-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstMarkCompetingRegionIntensitySplit
-- name    : Kyprianou.Ch06.firstMarkCompetingRegionIntensitySplit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:43:26.974822+00:00
-- url     : https://prove2.me/theorems/575fbff9-6547-4bd9-bf90-8872be6d2290
-- title:
--   Lemma 6.18: positive first-mark competing region intensity split
-- statement:
--   For any finite-intensity marked-Poisson region A and measurable test set C, the intensities of the two competing mark regions A∩C and A∖C add to the total intensity n(A), both as ENNReal and as finite real rates. This identity is needed to replace the denominator a+b in the exponential-race first-mark law by n(A).
-- source:
--   Kyprianou (2006), Lemma 6.18 (first marked Poisson arrival), printed pp.160–161.

import Mathlib
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstMarkCompetingRegionIntensitySplit
    {E : Type} [MeasurableSpace E] (n : Measure E)
    (A C : Set E) (hC : MeasurableSet C)
    (hFinite : n A < ⊤) :
    n (A ∩ C) + n (A \ C) = n A ∧
    (n (A ∩ C)).toReal + (n (A \ C)).toReal =
      (n A).toReal := by sorry
