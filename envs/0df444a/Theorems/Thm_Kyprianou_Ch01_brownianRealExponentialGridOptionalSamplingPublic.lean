-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianRealExponentialGridOptionalSamplingPublic
-- name    : Kyprianou.Ch01.brownianRealExponentialGridOptionalSamplingPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T09:53:15.124532+00:00
-- url     : https://prove2.me/theorems/4eca2e58-9b56-4a6e-a1e8-50112db42fa7
-- title:
--   Bounded-grid optional sampling for arbitrary real Brownian exponential parameters
-- statement:
--   For any real parameter theta, the compensated Brownian exponential exp(theta X_t minus psi(theta)t) has expected value one at every bounded natural-past-measurable integer-grid stopping index, where psi(theta) = sigma²theta²/2 + gamma theta. This strengthens the already proved positive-discount-root finite-grid result to 2theta, permitting a uniform second-moment bound for the original stopped exponential and hence uniform integrability during grid refinement.
-- source:
--   Kyprianou (2006) Exercise 1.10(i)-(ii), printed solution page 306, and published Prove2Me finiteGridOptionalStoppingEventwise (28b5b07b) and brownianRealExponentialMartingale (9fa7ef09). Public counterpart derived from an earlier accepted private proof; public finite-grid helper is a genuine prerequisite.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_le_ambient
import Theorems.Thm_Kyprianou_Ch01_brownianRealExponentialMartingale
import Theorems.Thm_Kyprianou_Ch01_brownianRealExpMoment
import Theorems.Thm_Kyprianou_Ch01_finiteGridOptionalStoppingEventwisePublic
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianRealExponentialGridOptionalSamplingPublic
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (sigma gamma theta : ℝ)
    (hsigma : 0 < sigma)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (delta : ℝ≥0) (τ : Ω → ℕ) (N : ℕ)
    (hBound : ∀ ω, τ ω ≤ N)
    (hStop : ∀ n, n < N →
      @MeasurableSet Ω (naturalSigma X ((n : ℝ≥0) * delta))
        {ω | n < τ ω}) :
    let psi : ℝ := sigma ^ 2 * theta ^ 2 / 2 + gamma * theta
    Integrable (fun ω => Real.exp
      (theta * X ((τ ω : ℝ≥0) * delta) ω -
        psi * (((τ ω : ℝ≥0) * delta) : ℝ))) P ∧
    (∫ ω, Real.exp (theta * X ((τ ω : ℝ≥0) * delta) ω -
        psi * (((τ ω : ℝ≥0) * delta) : ℝ)) ∂P) = 1 := by sorry
