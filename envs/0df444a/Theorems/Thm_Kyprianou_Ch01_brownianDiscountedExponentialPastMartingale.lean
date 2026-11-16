-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianDiscountedExponentialPastMartingale
-- name    : Kyprianou.Ch01.brownianDiscountedExponentialPastMartingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:27:52.089456+00:00
-- url     : https://prove2.me/theorems/2ed1f086-3711-4e9f-9f0e-40eefa4368ee
-- title:
--   Discounted Brownian adjustment exponential is a true natural-filtration martingale in conditional-integral form
-- statement:
--   The positive Brownian adjustment parameter theta solves sigma²theta²/2+gamma theta=q. Substitution in the previously Proved real Brownian exponential-martingale theorem gives the exact q-discounted exponential conditional-integral identity on every event in the original natural filtration, for all deterministic s≤t, plus integrability. This is the explicit true martingale required in the optional stopping argument for the Brownian upper-passage formula, without assuming a stopping-time theorem or passage-time finiteness.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10(ii), Brownian exponential-martingale proof.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianDiscountedExponentialPastMartingale
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q)
    (hX : Kyprianou.Ch01.IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    let theta : ℝ := (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    ∀ (s t : ℝ≥0), s ≤ t →
      Integrable (fun ω => Real.exp (theta * X t ω - q * (t : ℝ))) P ∧
      ∀ A : Set Ω,
        @MeasurableSet Ω (Kyprianou.Ch01.naturalSigma X s) A →
        (∫ ω in A, Real.exp (theta * X t ω - q * (t : ℝ)) ∂P) =
        (∫ ω in A, Real.exp (theta * X s ω - q * (s : ℝ)) ∂P) := by sorry
