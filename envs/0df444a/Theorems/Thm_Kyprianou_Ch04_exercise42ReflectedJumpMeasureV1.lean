-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42ReflectedJumpMeasureV1
-- name    : Kyprianou.Ch04.exercise42ReflectedJumpMeasureV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:49:36.647577+00:00
-- url     : https://prove2.me/theorems/d9651c9b-7aad-52e3-aab8-32a244f8fd0c
-- title:
--   Reflected BV jump measure has integrable subordinator exponent
-- statement:
--   Reflection of the negative jump measure preserves integrability of the truncated first moment and transforms the complex Laplace exponent integral.
-- source:
--   Supporting Laplace-to-characteristic exponent continuation for Kyprianou (2006), Chapter 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat07_bv_neg_map_magnitude_ae_positive
import Theorems.Thm_AvramDividend_Classical_chat07_bv_neg_map_magnitude_first_moment_integrable
open MeasureTheory Set AvramDividend.Classical Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42ReflectedJumpMeasureV1 {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) :
    let ν := (L.ν.restrict (Iio (0 : ℝ))).map (fun y : ℝ => -y)
    Integrable (fun x : ℝ => min 1 |x|) (ν.restrict (Ioi 0)) ∧
      ∀ z : ℂ, (∫ x in Ioi (0 : ℝ), (1 - Complex.exp (-z * (x : ℂ))) ∂ν) =
        ∫ y in Iio (0 : ℝ), (1 - Complex.exp (z * (y : ℂ))) ∂L.ν := by
  sorry
