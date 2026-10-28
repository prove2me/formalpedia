-- Prove2me | Theorems.Thm_OnlineNRM_TSFixed_posterior_matching_gap_covariance_identity
-- name    : OnlineNRM.TSFixed.posterior_matching_gap_covariance_identity
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T18:31:47.028523+00:00
-- url     : https://prove2.me/theorems/7af433ea-6c57-49ce-ab83-35f6286fc825
-- title:
--   Posterior resampling expresses the expected selector gap as diagonal oracle covariances
-- statement:
--   Posterior matching expresses the expected true-selector minus sampled-selector objective as the sum of history-centered diagonal oracle covariances. Extend matching to bounded selector coordinates, pull out the latent mean rewards, and expand the integrable finite objective. Neither optimality nor the offer and demand-observation laws are required. The none contribution vanishes, including when all selector mass is unused.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Definitions.Def_OnlineNRM_TSFixed_EntropyExperiment

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem OnlineNRM.TSFixed.posterior_matching_gap_covariance_identity
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
        condProb P (histSigma A D t) (θ ⁻¹' C)) :
    (∫ ω, lpObj p (meanDemand F (θ ω)) (xsel (θ ω)) -
      lpObj p (meanDemand F (θ ω)) (xsel (θs t ω)) ∂P) =
      ∑ a : Option (Fin K), weightedOracleCovariance P (histSigma A D t)
        (fun ω b => oracleActionWeights xsel (θ ω) b)
        (fun ω b => oracleMeanReward p F (θ ω) b) a := by sorry
