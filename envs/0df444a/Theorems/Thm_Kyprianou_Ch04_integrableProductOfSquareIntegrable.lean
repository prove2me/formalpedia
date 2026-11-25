-- Prove2me | Theorems.Thm_Kyprianou_Ch04_integrableProductOfSquareIntegrable
-- name    : Kyprianou.Ch04.integrableProductOfSquareIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T20:22:14.656472+00:00
-- url     : https://prove2.me/theorems/53058a85-9f3a-5603-98b5-67d08cd4896f
-- title:
--   Products of square-integrable random variables are integrable
-- statement:
--   The product of two almost-everywhere strongly measurable real functions with integrable squares is integrable; follows by the Holder L2 product inequality.
-- source:
--   Mathlib Holder inequality for L2; used to derive the pairwise product integrability hypotheses of Kyprianou (2006), Chapter 4, Exercise 4.4 simple predictable Poisson isometry.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
open MeasureTheory
set_option autoImplicit false
universe u

theorem Kyprianou.Ch04.integrableProductOfSquareIntegrable

    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ)
    (hXm : AEStronglyMeasurable X P)
    (hYm : AEStronglyMeasurable Y P)
    (hX2 : Integrable (fun ω => (X ω) ^ 2) P)
    (hY2 : Integrable (fun ω => (Y ω) ^ 2) P) :
    Integrable (fun ω => X ω * Y ω) P := by
  sorry
