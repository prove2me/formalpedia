-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianZeroDiscountPositiveDrift
-- name    : Kyprianou.Ch01.inverseGaussianZeroDiscountPositiveDrift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T21:40:52.35908+00:00
-- url     : https://prove2.me/theorems/a6233c88-7c64-4dd7-a1c1-27d4f4c4a001
-- title:
--   Positive-drift Brownian upper first passage has unit zero-discount Laplace mass
-- statement:
--   For Brownian motion with positive drift b and unit volatility, the positive-q discounted upper first-passage Laplace transform from the existing Brownian theorem converges to one as q decreases to zero, since sqrt(b²)=b for b>0. Use the explicit positive sequence q_n=1/(n+1), pointwise payoff convergence for finite or infinite passage, the constant probability-integrable bound 1, and Bochner dominated convergence to obtain both integrability at q=0 and expectation one. This source-faithful endpoint is required by the inverse-Gaussian first-passage transform when q≥0.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5 and Exercise 1.6, positive-drift Brownian first passage.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianZeroDiscountPositiveDrift
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (b s : ℝ)
    (hb : 0 < b) (hs : 0 < s)
    (hB : Kyprianou.Ch01.IsLinearBrownian P X 1 b)
    (hmeas : ∀ t : ℝ≥0, Measurable (X t)) :
    Integrable (Kyprianou.Ch01.passageLaplace
      (Kyprianou.Ch01.firstUpperPassage X s) 0) P ∧
    (∫ ω, Kyprianou.Ch01.passageLaplace
      (Kyprianou.Ch01.firstUpperPassage X s) 0 ω ∂P) = 1 := by sorry
