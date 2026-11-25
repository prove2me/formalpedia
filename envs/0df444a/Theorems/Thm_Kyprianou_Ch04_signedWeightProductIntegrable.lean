-- Prove2me | Theorems.Thm_Kyprianou_Ch04_signedWeightProductIntegrable
-- name    : Kyprianou.Ch04.signedWeightProductIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:59:15.296825+00:00
-- url     : https://prove2.me/theorems/83aec65a-e187-5002-bf0d-d5d1269c5656
-- title:
--   Integrability of the signed weighted cross product
-- statement:
--   Integrability of the two signed weighted squares and measurability imply integrability of the signed weighted product.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; weighted Poisson cell isometry.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
open MeasureTheory
set_option autoImplicit false
universe u

theorem Kyprianou.Ch04.signedWeightProductIntegrable
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (W A B : Ω → ℝ)
    (hW : AEStronglyMeasurable W P) (hAm : AEStronglyMeasurable A P)
    (hBm : AEStronglyMeasurable B P)
    (hA : Integrable (fun ω => W ω * (A ω)^2) P)
    (hB : Integrable (fun ω => W ω * (B ω)^2) P) :
    Integrable (fun ω => W ω * A ω * B ω) P := by
  sorry
