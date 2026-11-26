-- Prove2me | Theorems.Thm_Kyprianou_Ch04_weightedOverlapCovarianceExpansion
-- name    : Kyprianou.Ch04.weightedOverlapCovarianceExpansion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:25:04.584207+00:00
-- url     : https://prove2.me/theorems/a6d9da17-decb-594f-be0b-3f0f48e1f354
-- title:
--   Weighted covariance of sums with a common component
-- statement:
--   Expand two almost-sure decompositions with a shared component; the three orthogonal cross terms integrate to zero, leaving the weighted shared square.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; covariance expansion.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory
set_option autoImplicit false
universe u

theorem Kyprianou.Ch04.weightedOverlapCovarianceExpansion
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (W X Y U V Z : Ω → ℝ)
    (hX : X =ᵐ[P] fun ω => U ω + V ω)
    (hY : Y =ᵐ[P] fun ω => V ω + Z ω)
    (hUV : Integrable (fun ω => W ω * U ω * V ω) P)
    (hUZ : Integrable (fun ω => W ω * U ω * Z ω) P)
    (hVZ : Integrable (fun ω => W ω * V ω * Z ω) P)
    (hVV : Integrable (fun ω => W ω * (V ω)^2) P)
    (eUV : (∫ ω, W ω * U ω * V ω ∂P) = 0)
    (eUZ : (∫ ω, W ω * U ω * Z ω ∂P) = 0)
    (eVZ : (∫ ω, W ω * V ω * Z ω ∂P) = 0) :
    (∫ ω, W ω * X ω * Y ω ∂P) =
      ∫ ω, W ω * (V ω)^2 ∂P := by
  sorry
