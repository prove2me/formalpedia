-- Prove2me | Theorems.Thm_OnlineNRM_TSFixed_posterior_matching_finite_oracle_experiment
-- name    : OnlineNRM.TSFixed.posterior_matching_finite_oracle_experiment
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T18:31:10.007498+00:00
-- url     : https://prove2.me/theorems/96bc41fc-48b6-489f-9824-af4457d6e65d
-- title:
--   Posterior sampling and demand laws induce a bounded finite oracle experiment
-- statement:
--   The posterior-sampling, randomized-offer, and bounded conditional-demand assumptions imply the abstract finite oracle experiment fields. Prove these using conditional-expectation towers, bounded-function extensions of the eventwise laws, kernel-integral measurability, and support bounds. The shut-off action has zero reward and unused selector mass. All hypotheses remain valid at t = 0, K = 1, and N = 0.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Definitions.Def_OnlineNRM_TSFixed_EntropyExperiment

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem OnlineNRM.TSFixed.posterior_matching_finite_oracle_experiment
    {N K : ℕ} (hK : 1 ≤ K)
    (p : Fin N → Fin K → ℝ) (dbar : Fin N → ℝ)
    (hp : ∀ i k, 0 ≤ p i k)
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (F : Kernel (Θ × Fin K) (Fin N → ℝ)) [IsMarkovKernel F]
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (θs : ℕ → Ω → Θ)
    (A : ℕ → Ω → Option (Fin K)) (D : ℕ → Ω → Fin N → ℝ)
    (xsel : Θ → Fin K → ℝ) (t : ℕ)
    (hθ : Measurable θ) (hθs : ∀ s, Measurable (θs s))
    (hA : ∀ s, Measurable (A s)) (hD : ∀ s, Measurable (D s))
    (hx : Measurable xsel)
    (hx0 : ∀ ρ k, 0 ≤ xsel ρ k)
    (hx1 : ∀ ρ, ∑ k : Fin K, xsel ρ k ≤ 1)
    (hsample : ∀ C : Set Θ, MeasurableSet C →
      condProb P (pastSigma θ θs A D t) (θs t ⁻¹' C) =ᵐ[P]
        condProb P (histSigma A D t) (θ ⁻¹' C))
    (hoffer : ∀ k : Fin K,
      condProb P (pastSigma θ θs A D t ⊔
          MeasurableSpace.comap (θs t) inferInstance) (A t ⁻¹' {some k}) =ᵐ[P]
        fun ω => xsel (θs t ω) k)
    (hdemand : ∀ B : Set (Fin N → ℝ), MeasurableSet B →
      condProb P (pastSigma θ θs A D t ⊔
          MeasurableSpace.comap (θs t) inferInstance ⊔
          MeasurableSpace.comap (A t) inferInstance) (D t ⁻¹' B) =ᵐ[P]
        fun ω => (demandLaw F (θ ω) (A t ω) B).toReal) :
    IsFiniteOracleExperiment P (histSigma A D t) (pastSigma θ θs A D t)
      (histSigma A D (t + 1))
      (fun ω a => oracleActionWeights xsel (θ ω) a)
      (fun ω a => oracleMeanReward p F (θ ω) a)
      (A t) (observedPriceReward p (A t) (D t)) (pmax p dbar) := by sorry
