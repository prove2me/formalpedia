-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianDiscountedUpperPassage
-- name    : Kyprianou.Ch01.brownianDiscountedUpperPassage
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T10:37:46.783096+00:00
-- url     : https://prove2.me/theorems/099cb1a3-ea9c-4afd-af51-13c8a4f55c75
-- title:
--   Exercise 1.10(ii): upward Brownian discounted first-passage transform
-- statement:
--   For a Brownian motion of positive diffusion scaling σ with drift γ, the Laplace transform of its first strict upcrossing time above x>0 has the exact coefficient (sqrt(γ²+2σ²q)-γ)/σ², for q>0. Together with the existing downward formula, this covers both conclusions of Exercise 1.10(ii).
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10(ii), printed page 32.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianDiscountedUpperPassage
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q x : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (hx : 0 < x)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    Integrable (passageLaplace (firstUpperPassage X x) q) P ∧
    (∫ ω, passageLaplace (firstUpperPassage X x) q ω ∂P) =
      Real.exp (-x * ((Real.sqrt
        (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2)) := by
  sorry
