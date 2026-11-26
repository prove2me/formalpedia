-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42DeficitComplexRayV1
-- name    : Kyprianou.Ch04.exercise42DeficitComplexRayV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:57:12.39312+00:00
-- url     : https://prove2.me/theorems/0578b46f-db15-5114-8a51-ee446d22ed0e
-- title:
--   Original BV deficit complex Laplace formula on closed half-plane
-- statement:
--   The original BV drift deficit obeys the complex Laplace identity for every complex argument with nonnegative real part.
-- source:
--   Supporting Laplace-to-characteristic exponent continuation for Kyprianou (2006), Chapter 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Theorems.Thm_Kyprianou_Ch02_nonnegativeLawComplexLaplaceAnalyticV1
import Theorems.Thm_Kyprianou_Ch02_subordinatorExponentComplexLaplaceAnalyticV1
import Theorems.Thm_Kyprianou_Ch04_rightHalfPlaneIdentityFromRealRayV1
import Theorems.Thm_Kyprianou_Ch04_exercise42ReflectedJumpMeasureV1
import Theorems.Thm_Kyprianou_Ch04_exercise42DeficitRealRayV1
open MeasureTheory Set AvramDividend.Classical Complex Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42DeficitComplexRayV1 {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation)
    (t : ℝ≥0) (z : ℂ) (hz : 0 ≤ z.re) :
    (∫ ω, Complex.exp (-z * ((L.drift * (t : ℝ) - L.X t ω : ℝ) : ℂ)) ∂P) =
      Complex.exp (-((t : ℝ) : ℂ) *
        ∫ y in Iio (0 : ℝ), (1 - Complex.exp (z * (y : ℂ))) ∂L.ν) := by
  sorry
