-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianDiscountedLowerPassage
-- name    : Kyprianou.Ch01.brownianDiscountedLowerPassage
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:24:40.128265+00:00
-- url     : https://prove2.me/theorems/09a946b2-6632-4fef-b9d8-cf2f1968a282
-- title:
--   Exercise 1.10(ii): discounted Brownian lower-passage identity
-- statement:
--   Kyprianou (2006) Exercise 1.10(ii). For Brownian motion with drift γ and volatility σ>0, prove that the first passage below −a, a≥0, has discounted Laplace transform exp(−a(√(γ²+2σ²q)+γ)/σ²) for q>0. The source applies the exponential martingale and optional stopping and then differentiates the candidate barrier objective in Exercise 1.10(iii). The target is a genuine analytic input for Theorem 1.13 and does not assume optimality.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10(ii), printed p. 32.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianDiscountedLowerPassage
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q a : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (ha : 0 ≤ a)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    Integrable
      (passageLaplace (firstLowerPassage X 0 (-a)) q) P ∧
    (∫ ω, passageLaplace (firstLowerPassage X 0 (-a)) q ω ∂P) =
      Real.exp (-a * ((Real.sqrt
        (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) / sigma ^ 2)) := by
  sorry
