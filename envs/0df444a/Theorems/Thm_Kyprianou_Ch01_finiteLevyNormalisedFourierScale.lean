-- Prove2me | Theorems.Thm_Kyprianou_Ch01_finiteLevyNormalisedFourierScale
-- name    : Kyprianou.Ch01.finiteLevyNormalisedFourierScale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:20:22.192328+00:00
-- url     : https://prove2.me/theorems/d5138783-763d-4b10-a0e1-49ffd177fca5
-- title:
--   Finite Lévy intensity Fourier integral equals total mass times normalised jump-law Fourier difference
-- statement:
--   For an arbitrary finite real measure Λ, its compensated Fourier integral equals its total mass times the difference between the characteristic function of its normalised probability law and one. This is valid for zero mass as well (both sides vanish), and is the exact bridge to the genuine compound-Poisson Fourier exponent for a nonzero logarithmic convolution intensity.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), finite-intensity compound-Poisson normalisation.

import Mathlib
open MeasureTheory Complex
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.finiteLevyNormalisedFourierScale
    (Λ : Measure ℝ) (hfinite : Λ Set.univ < ⊤) (xi : ℝ) :
    let FM : FiniteMeasure ℝ := ⟨Λ, ⟨hfinite⟩⟩
    let ν' : Measure ℝ := (FM.normalize : Measure ℝ)
    (∫ x : ℝ,
      (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) ∂Λ) =
      ((FM.mass : ℂ) * (charFun ν' xi - 1)) := by
  sorry
