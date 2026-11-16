-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianRealExponentialMartingale
-- name    : Kyprianou.Ch01.brownianRealExponentialMartingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:37:48.833559+00:00
-- url     : https://prove2.me/theorems/9fa7ef09-6cda-443b-88a6-4635841a3331
-- title:
--   Exercise 1.10(i): real Brownian exponential martingale
-- statement:
--   For Brownian motion with drift γ and diffusion scaling σ>0, exp(θ X_t - (σ² θ²/2 + γθ)t) is an integrable martingale with respect to the natural filtration, for each real θ. This is the real moment-generating exponential required in Exercise 1.10(i), rather than only the complex characteristic exponential.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10(i), printed page 32.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianRealExponentialMartingale
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma theta : ℝ)
    (hsigma : 0 < sigma)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    let psi : ℝ := sigma ^ 2 * theta ^ 2 / 2 + gamma * theta
    let M : ℝ≥0 → Ω → ℝ :=
      fun t ω => Real.exp (theta * X t ω - psi * (t : ℝ))
    ∀ (s t : ℝ≥0), s ≤ t →
      Integrable (M t) P ∧
      ∀ A : Set Ω,
        @MeasurableSet Ω (naturalSigma X s) A →
        (∫ ω in A, M t ω ∂P) = (∫ ω in A, M s ω ∂P) := by
  sorry
