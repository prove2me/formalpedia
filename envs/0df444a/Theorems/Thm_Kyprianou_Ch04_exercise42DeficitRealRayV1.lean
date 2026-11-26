-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42DeficitRealRayV1
-- name    : Kyprianou.Ch04.exercise42DeficitRealRayV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:53:04.99334+00:00
-- url     : https://prove2.me/theorems/dd3e74fb-80b1-553a-9fc1-a7f42157d8a3
-- title:
--   Original drift deficit complex Laplace formula on the real ray
-- statement:
--   The actual BV drift deficit obeys the complex-valued Laplace identity at every real argument at least one.
-- source:
--   Supporting Laplace-to-characteristic exponent continuation for Kyprianou (2006), Chapter 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_normalised_laplace
open MeasureTheory Set AvramDividend.Classical Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42DeficitRealRayV1 {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation)
    (t : ℝ≥0) (θ : ℝ) (hθ : 1 ≤ θ) :
    (∫ ω, Complex.exp (-(θ : ℂ) * ((L.drift * (t : ℝ) - L.X t ω : ℝ) : ℂ)) ∂P) =
      Complex.exp (-((t : ℝ) : ℂ) *
        ∫ y in Iio (0 : ℝ), (1 - Complex.exp ((θ : ℂ) * (y : ℂ))) ∂L.ν) := by
  sorry
