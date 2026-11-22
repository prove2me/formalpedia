-- Prove2me | Theorems.Thm_Kyprianou_Ch01_queueExponentialMartingaleAndPassage
-- name    : Kyprianou.Ch01.queueExponentialMartingaleAndPassage
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:23:46.164528+00:00
-- url     : https://prove2.me/theorems/840dd61c-3966-4335-8f05-458232077c16
-- title:
--   Exercise 1.9(ii): exponential martingale and exact M/G/1 passage probability
-- statement:
--   Kyprianou Exercise 1.9(ii), printed p. 31. Under overloaded M/G/1 conditions λμ>1, strict positivity of service times and the positive Cramér root θ*>0 of ψ(θ)=θ−λ∫(1−e^(−θz))F(dz), show the process exp(θ*X_t−tψ(θ*)) is a martingale in its natural filtration. Use stopped optional sampling and absence of positive jumps to derive P(sup_{t≥0}X_t>x)=e^(−θ*x) for x>0. The exact passage probability and martingale eventwise-integral equality are conclusions; neither is assumed.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.9(ii), printed p. 31.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.queueExponentialMartingaleAndPassage
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hDriver : IsCompoundPoissonDriver arrival claims rate F P)
    (hPos : F (Set.Iic (0 : ℝ)) = 0)
    (hIntegrable : Integrable (fun z : ℝ => z) F)
    (mu : ℝ) (hMean : (∫ z, z ∂F) = mu)
    (hOverload : 1 < (rate : ℝ) * mu)
    (theta : ℝ) (hTheta : 0 < theta)
    (hRoot : queueLaplaceExponent rate F theta = 0) :
    let X : ℝ≥0 → Ω → ℝ := riskSurplus arrival claims 1 0
    let M : ℝ≥0 → Ω → ℝ :=
      fun t ω =>
        Real.exp (theta * X t ω -
          queueLaplaceExponent rate F theta * (t : ℝ))
    (∀ (s t : ℝ≥0), s ≤ t →
      Integrable (M t) P ∧
      ∀ A : Set Ω,
        @MeasurableSet Ω (naturalSigma X s) A →
        (∫ ω in A, M t ω ∂P) =
          (∫ ω in A, M s ω ∂P)) ∧
    ∀ x : ℝ, 0 < x →
      (P {ω | ∃ t : ℝ≥0, 0 < t ∧ x < X t ω}).toReal =
        Real.exp (-theta * x) := by
  sorry
