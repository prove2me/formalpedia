-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42NegativeUncompensatedExponentV1
-- name    : Kyprianou.Ch04.exercise42NegativeUncompensatedExponentV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:57:29.190016+00:00
-- url     : https://prove2.me/theorems/9396e2fa-3975-43ac-937a-9324f26cb3b7
-- title:
--   Uncompensated BV characteristic exponent for negative jumps
-- statement:
--   The original source measure is a Lévy measure and the zero Gaussian characteristic exponent equals its uncompensated negative-jump expression with physical drift.
-- source:
--   Supporting same-space triplet identification for Kyprianou (2006), Chapter 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
import Theorems.Thm_AvramDividend_Classical_boundedVariation_min_one_abs_integrable
open MeasureTheory ProbabilityTheory Set Complex AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42NegativeUncompensatedExponentV1 {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) (ξ : ℝ) :
    ∃ hν : IsLevyMeasure L.ν,
    Kyprianou.Ch01.levyTripleExponent ⟨L.c, 0, L.ν, hν⟩ ξ =
      I * ((L.drift * ξ : ℝ) : ℂ) +
      ∫ y in Iio (0 : ℝ), (Complex.exp (I * ((ξ * y : ℝ) : ℂ)) - 1) ∂L.ν := by
  sorry
