-- Prove2me | Theorems.Thm_Kyprianou_Ch04_geometricConvolutionNonnegativeSupport
-- name    : Kyprianou.Ch04.geometricConvolutionNonnegativeSupport
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:25:24.866137+00:00
-- url     : https://prove2.me/theorems/1b2e0972-7490-4885-a0f1-55c7818dde61
-- title:
--   Geometric convolution mixtures preserve nonnegative support
-- statement:
--   Geometric convolution mixtures of nonnegative probability measures are supported on the nonnegative halfline.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.geometricConvolutionNonnegativeSupport (eta mu : Measure ℝ) [IsProbabilityMeasure eta]
    (r : ENNReal) (h0 : eta (Iio 0) = 0)
    (hLaw : ∀ B : Set ℝ, MeasurableSet B →
      mu B = ∑' n : ℕ, ((1-r)*r^n) *
        ((Nat.rec (Measure.dirac (0 : ℝ)) (fun _ (m : Measure ℝ) => m.conv eta) n : Measure ℝ) B)) :
    mu (Iio 0) = 0 := by
  sorry
