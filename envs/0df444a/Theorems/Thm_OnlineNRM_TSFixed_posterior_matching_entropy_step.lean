-- Prove2me | Theorems.Thm_OnlineNRM_TSFixed_posterior_matching_entropy_step
-- name    : OnlineNRM.TSFixed.posterior_matching_entropy_step
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T14:50:53.1807+00:00
-- url     : https://prove2.me/theorems/908872e4-5a7e-4fac-85db-8178732cd46c
-- title:
--   One-period squared oracle gap is paid for by posterior oracle entropy decrease
-- statement:
--   At one period satisfying posterior sampling, randomized offers, and the bounded demand feedback law, expected oracle entropy cannot increase. The square of the unconditional expected selector gap is at most pmax squared times (K+1)/2 times the entropy decrease. The selector may be nonoptimal and may assign mass to shut-off.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run
import Definitions.Def_OnlineNRM_TSFixed_OracleEntropy

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem OnlineNRM.TSFixed.posterior_matching_entropy_step
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
    0 ≤ (finitePosteriorEntropy P (histSigma A D t)
        (fun ω a => oracleActionWeights xsel (θ ω) a) -
      finitePosteriorEntropy P (histSigma A D (t + 1))
        (fun ω a => oracleActionWeights xsel (θ ω) a)) ∧
    (∫ ω, lpObj p (meanDemand F (θ ω)) (xsel (θ ω)) -
      lpObj p (meanDemand F (θ ω)) (xsel (θs t ω)) ∂P) ^ 2 ≤
      (pmax p dbar) ^ 2 * (((K : ℝ) + 1) / 2) *
        (finitePosteriorEntropy P (histSigma A D t)
        (fun ω a => oracleActionWeights xsel (θ ω) a) -
          finitePosteriorEntropy P (histSigma A D (t + 1))
        (fun ω a => oracleActionWeights xsel (θ ω) a)) := by sorry
