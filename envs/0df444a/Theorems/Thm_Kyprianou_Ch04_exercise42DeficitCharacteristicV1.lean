-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42DeficitCharacteristicV1
-- name    : Kyprianou.Ch04.exercise42DeficitCharacteristicV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:02:02.20425+00:00
-- url     : https://prove2.me/theorems/ec9d0b13-7db6-51cf-87b4-d37b078f6091
-- title:
--   Original BV characteristic function from the deficit transform
-- statement:
--   The original spectrally negative BV process has the uncompensated characteristic exponent with its source physical drift and negative jump measure.
-- source:
--   Supporting same-space triplet identification for Kyprianou (2006), Chapter 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Complex AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42DeficitCharacteristicV1 {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation)
    (t : ℝ≥0) (ξ : ℝ) :
    charFun (P.map (L.X t)) ξ =
      Complex.exp (((t : ℝ) : ℂ) *
        (I * ((L.drift * ξ : ℝ) : ℂ) +
          ∫ y in Iio (0 : ℝ), (Complex.exp (I * ((ξ * y : ℝ) : ℂ)) - 1) ∂L.ν)) := by
  sorry
