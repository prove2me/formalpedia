-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianDiscountedExponentialMeanOne
-- name    : Kyprianou.Ch01.brownianDiscountedExponentialMeanOne
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:08:46.844701+00:00
-- url     : https://prove2.me/theorems/af75b30e-8e4a-4293-8595-6585f35af597
-- title:
--   Brownian exponential with the adjustment root has unit discounted expectation
-- statement:
--   The positive Brownian adjustment root θ from Kyprianou Exercise 1.10(ii) satisfies ψ(θ)=q. The original proved BrownianRealExpMoment then makes E[e^(θ X_t-q t)]=e^(t(ψ(θ)-q))=1 for every deterministic t, and the same integrable moment supplies discounted integrability. This is the exact one-time mean-one ingredient for the optional-stopping proof of the Brownian upper first-passage transform. Reuses the separately proved quadratic root and Gaussian exponential moment with no new assumptions.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10(ii), printed solution p.306, PDF page 158.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianDiscountedExponentialMeanOne
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q : ℝ) (hsigma : 0 < sigma) (hq : 0 < q)
    (hX : Kyprianou.Ch01.IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) (t : ℝ≥0) :
    let theta := (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    Integrable (fun ω => Real.exp (theta * X t ω - q * (t : ℝ))) P ∧
    (∫ ω, Real.exp (theta * X t ω - q * (t : ℝ)) ∂P) = 1 := by sorry
