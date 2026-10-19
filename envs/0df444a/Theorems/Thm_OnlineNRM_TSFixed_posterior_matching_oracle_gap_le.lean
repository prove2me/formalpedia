-- Prove2me | Theorems.Thm_OnlineNRM_TSFixed_posterior_matching_oracle_gap_le
-- name    : OnlineNRM.TSFixed.posterior_matching_oracle_gap_le
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T14:28:16.324528+00:00
-- url     : https://prove2.me/theorems/891e5be1-6da5-47fc-93f5-d371c3d320ab
-- title:
--   Finite-oracle regret bound for posterior matching with randomized selectors
-- statement:
--   For any measurable selector of nonnegative arm probabilities summing to at most one, posterior sampling followed by that selector has cumulative expected reward gap against the true-parameter selector at most pmax times sqrt(T (K+1) log(K+1) / 2). The unused probability is the zero-reward shut-off action. LP optimality and resource constraints are not assumed.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Mathlib
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem OnlineNRM.TSFixed.posterior_matching_oracle_gap_le
    {N K T : ℕ} (hK : 1 ≤ K)
    (p : Fin N → Fin K → ℝ) (dbar : Fin N → ℝ)
    (hp : ∀ i k, 0 ≤ p i k)
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (F : Kernel (Θ × Fin K) (Fin N → ℝ)) [IsMarkovKernel F]
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (θs : ℕ → Ω → Θ)
    (A : ℕ → Ω → Option (Fin K)) (D : ℕ → Ω → Fin N → ℝ)
    (xsel : Θ → Fin K → ℝ)
    (hθ : Measurable θ) (hθs : ∀ t, Measurable (θs t))
    (hA : ∀ t, Measurable (A t)) (hD : ∀ t, Measurable (D t))
    (hx : Measurable xsel)
    (hx0 : ∀ ρ k, 0 ≤ xsel ρ k)
    (hx1 : ∀ ρ, ∑ k : Fin K, xsel ρ k ≤ 1)
    (hsample : ∀ t < T, ∀ C : Set Θ, MeasurableSet C →
      condProb P (pastSigma θ θs A D t) (θs t ⁻¹' C) =ᵐ[P]
        condProb P (histSigma A D t) (θ ⁻¹' C))
    (hoffer : ∀ t < T, ∀ k : Fin K,
      condProb P (pastSigma θ θs A D t ⊔
          MeasurableSpace.comap (θs t) inferInstance) (A t ⁻¹' {some k}) =ᵐ[P]
        fun ω => xsel (θs t ω) k)
    (hdemand : ∀ t < T, ∀ B : Set (Fin N → ℝ), MeasurableSet B →
      condProb P (pastSigma θ θs A D t ⊔
          MeasurableSpace.comap (θs t) inferInstance ⊔
          MeasurableSpace.comap (A t) inferInstance) (D t ⁻¹' B) =ᵐ[P]
        fun ω => (demandLaw F (θ ω) (A t ω) B).toReal) :
    (∑ t ∈ Finset.range T,
      ∫ ω, lpObj p (meanDemand F (θ ω)) (xsel (θ ω)) -
        lpObj p (meanDemand F (θ ω)) (xsel (θs t ω)) ∂P) ≤
      pmax p dbar *
        Real.sqrt ((T : ℝ) * ((K : ℝ) + 1) * Real.log ((K : ℝ) + 1) / 2) := by sorry
