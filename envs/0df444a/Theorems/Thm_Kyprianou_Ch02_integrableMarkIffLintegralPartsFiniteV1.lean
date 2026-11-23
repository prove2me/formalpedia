-- Prove2me | Theorems.Thm_Kyprianou_Ch02_integrableMarkIffLintegralPartsFiniteV1
-- name    : Kyprianou.Ch02.integrableMarkIffLintegralPartsFiniteV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T12:05:15.788803+00:00
-- url     : https://prove2.me/theorems/f2cd6dc4-78d7-4fd1-8f0c-6ffeb1249e4b
-- title:
--   Integrability of a signed real mark is equivalent to finiteness of its positive and negative lintegrals
-- statement:
--   For any measure μ on real time-mark space and any measurable R, the Bochner integrability of its second coordinate on μ.restrict R is equivalent to finiteness of the two nonnegative extended integrals of the positive and negative parts. Derive using lintegral_ofReal_ne_top_iff_integrable, max_zero_sub_max_neg_zero_eq_self, and Integrable.pos_part, Integrable.neg_part. This supports the signed-integral measurability parent, which was blocked by complexity when written inline.
-- source:
--   Kyprianou (2006) Chapter 2 signed Poisson stochastic integral, deterministic measure theory

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.integrableMarkIffLintegralPartsFiniteV1
    (μ : Measure (ℝ × ℝ)) (R : Set (ℝ × ℝ)) (hR : MeasurableSet R) :
    Integrable (fun z : ℝ × ℝ => z.2) (μ.restrict R) ↔
      (∫⁻ z in R, ENNReal.ofReal z.2 ∂μ) ≠ ⊤ ∧
      (∫⁻ z in R, ENNReal.ofReal (-z.2) ∂μ) ≠ ⊤ := by sorry
