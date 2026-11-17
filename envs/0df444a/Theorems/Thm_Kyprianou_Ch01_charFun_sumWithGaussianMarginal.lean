-- Prove2me | Theorems.Thm_Kyprianou_Ch01_charFun_sumWithGaussianMarginal
-- name    : Kyprianou.Ch01.charFun_sumWithGaussianMarginal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:01:02.688434+00:00
-- url     : https://prove2.me/theorems/85724a17-9d77-44b8-a86d-8adc2f75dba8
-- title:
--   Product-space Gaussian plus independent real marginal characteristic-function factorisation
-- statement:
--   For any real-valued probability law μ and independent centred Gaussian law of variance v, the characteristic function of their sum on the product probability space equals the characteristic function of μ multiplied by the exactly scaled Gaussian factor exp(-v ξ²/2), for every real frequency ξ. This gives the explicit marginal Fourier identity for the Gaussian-plus-pure-jump Lévy process used in Kyprianou Chapter 1 Theorem 1.6.
-- source:
--   Mathlib pinned revision 0df444a360eaa60ab8c11dca51a86af692955474: ProbabilityTheory.charFun_map_add_prod_eq_mul and ProbabilityTheory.charFun_gaussianReal, source modules Mathlib.Probability.Independence.CharacteristicFunction and Mathlib.Probability.Distributions.Gaussian.Real.

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.Real
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.charFun_sumWithGaussianMarginal
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (v : ℝ≥0) (xi : ℝ) :
    charFun ((mu.prod (gaussianReal 0 v)).map
        (fun p : ℝ × ℝ => p.1 + p.2)) xi =
      charFun mu xi *
        Complex.exp (-((v : ℂ) * (xi : ℂ) ^ 2 / 2)) := by
  sorry
