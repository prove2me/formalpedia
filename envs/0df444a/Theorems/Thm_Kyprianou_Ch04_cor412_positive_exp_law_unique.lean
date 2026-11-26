-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_positive_exp_law_unique
-- name    : Kyprianou.Ch04.cor412_positive_exp_law_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:39:46.227579+00:00
-- url     : https://prove2.me/theorems/0c2829cb-cbb6-555d-9eef-fedaacda8bbd
-- title:
--   Positive-ray exponential transforms determine a measure with nonzero finite tilt
-- statement:
--   Equality of finite positive-ray exponential integrals determines the original measures when the exponential tilt is nonzero.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12, supporting lemma.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_measure_eq_of_pos_mgf_on_ray
import Theorems.Thm_Kyprianou_Ch04_cor412_exp_tilt_transform
open MeasureTheory Set Filter AvramDividend.Classical
open scoped ENNReal
set_option autoImplicit false

/-- Exponential tilting reduces equality of finite positive-ray exponential integrals to probability MGF uniqueness. -/

theorem Kyprianou.Ch04.cor412_positive_exp_law_unique (μ ν : Measure ℝ)
    (hμ : ∀ s : ℝ, 0 < s → (∫⁻ x, ENNReal.ofReal (Real.exp (s*x)) ∂μ) ≠ ⊤)
    (he : ∀ s : ℝ, 0 < s → (∫⁻ x, ENNReal.ofReal (Real.exp (s*x)) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (Real.exp (s*x)) ∂ν)
    (hc0 : (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂μ) ≠ 0) : μ = ν := by sorry
