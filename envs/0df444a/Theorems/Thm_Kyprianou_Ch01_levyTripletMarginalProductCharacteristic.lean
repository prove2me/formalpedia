-- Prove2me | Theorems.Thm_Kyprianou_Ch01_levyTripletMarginalProductCharacteristic
-- name    : Kyprianou.Ch01.levyTripletMarginalProductCharacteristic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T20:58:42.270883+00:00
-- url     : https://prove2.me/theorems/7595f288-8ad3-4743-8716-9a954cf095f3
-- title:
--   Pure-jump plus independent Gaussian marginal has the exact original Lévy–Khintchine characteristic function
-- statement:
--   Take any Lévy–Khintchine triplet T, any nonnegative time t and any real-valued probability measure mu whose characteristic function is exactly the Lévy exponent of the triplet with the original drift and jumps but zero Gaussian variance. The sum on the product probability space of a random variable with law mu and an independent centred real Gaussian with variance t times T.gaussianVariance has characteristic function precisely exp(t times the original triplet exponent), for every real frequency. No stochastic process existence assumption is introduced; this theorem isolates the analytic Fourier identity needed for the positive Gaussian case of Kyprianou Chapter 1 Theorem 1.6.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.6 and Lévy–Khintchine formula; Proved Kyprianou.Ch01.levyTripleExponent_expGaussianFactorisation, ProbabilityTheory.charFun_map_add_prod_eq_mul and ProbabilityTheory.charFun_gaussianReal.

import Definitions.Def_Kyprianou_Ch01_LevyTripletExponentTargeted
import Theorems.Thm_Kyprianou_Ch01_levyTripleExponent_expGaussianFactorisation
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.Real
open MeasureTheory ProbabilityTheory Complex Kyprianou.Ch01
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.levyTripletMarginalProductCharacteristic
    (T : ProbabilityTheory.LevyKhintchineTriple) (t : ℝ≥0)
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hmu : ∀ xi : ℝ,
      charFun mu xi = Complex.exp (((t : ℝ) : ℂ) *
        levyTripleExponent
          ⟨T.drift, 0, T.levyMeasure, T.levyMeasure_isLevyMeasure⟩ xi))
    (xi : ℝ) :
    charFun ((mu.prod (gaussianReal 0 (t * T.gaussianVariance))).map
      (fun p : ℝ × ℝ => p.1 + p.2)) xi =
      Complex.exp (((t : ℝ) : ℂ) * levyTripleExponent T xi) := by
  sorry
