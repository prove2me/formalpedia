-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianPassageZeroDiscount
-- name    : Kyprianou.Ch01.inverseGaussianPassageZeroDiscount
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T19:10:53.337416+00:00
-- url     : https://prove2.me/theorems/a011bacb-fdc2-4c4b-a6e8-e3f9334b63cd
-- title:
--   Positive-drift Brownian strict upward passage has zero-discount Laplace mass one
-- statement:
--   For a standard-variance Brownian Lévy process with positive drift, and a positive level, the strict first upward passage is almost surely finite. Equivalently, the zero-discount passage Laplace transform, defined as zero on infinite passage, integrates to one. This endpoint is the missing q=0 part of the inverse Gaussian first-passage Laplace formula, and can be proved by monotone convergence as q decreases to zero after the positive-q Brownian exponential-passage identity, or from Brownian strong law.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5 and Exercise 1.6(i), printed pp. 8–9, 28–29; technical zero-parameter child for published milestone 5109b042-f54f-4840-8300-3b46f5ada4c6.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.inverseGaussianPassageZeroDiscount
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (b s : ℝ)
    (hb : 0 < b) (hs : 0 < s)
    (hB : IsLinearBrownian P X 1 b)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    (∫ ω, passageLaplace (firstUpperPassage X s) (0 : ℝ) ω ∂P) = 1 := by
  sorry
