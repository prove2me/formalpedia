-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_exponential_convolution_moment
-- name    : KSATSingleFlip.Connect.exponential_convolution_moment
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:42:12.405693+00:00
-- url     : https://prove2.me/theorems/f23cc91f-0b68-4d0e-b82e-f39886a0a44d
-- title:
--   Exponential moment of a convolution of finite measures
-- statement:
--   For real measures μ and ν with ν s-finite, the extended exponential moment of their additive convolution is the product of their extended exponential moments. This is a kernel ingredient for the compound-Poisson transform in the soft-field recursion.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Definition 4.2 and proof of Lemma 4.5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

theorem KSATSingleFlip.Connect.exponential_convolution_moment (μ ν : Measure ℝ) [SFinite ν] (c : ℝ) :
    (∫⁻ z, ENNReal.ofReal (Real.exp (c*z)) ∂(μ ∗ ν)) =
      (∫⁻ x, ENNReal.ofReal (Real.exp (c*x)) ∂μ) *
      (∫⁻ y, ENNReal.ofReal (Real.exp (c*y)) ∂ν) := by sorry
