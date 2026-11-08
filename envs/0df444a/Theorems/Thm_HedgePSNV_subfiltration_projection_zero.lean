-- Prove2me | Theorems.Thm_HedgePSNV_subfiltration_projection_zero
-- name    : HedgePSNV.subfiltration_projection_zero
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T15:36:29.554543+00:00
-- url     : https://prove2.me/theorems/1cabd088-aeb4-4324-98c6-e0687cc9857d
-- title:
--   Projection onto a Brownian subfiltration vanishes under orthogonality
-- statement:
--   For filtrations $\mathcal K\subseteq\mathcal F$ for which $W$ is Brownian and $\mathcal K_T$-conditioning commutes as in H1, if $\Theta=\mathbb E[\theta\mid\mathcal K_T]=\mathbb E[\theta_B\mid\mathcal K_T]$ is orthogonal to bounded $\mathcal K_t$-measurable variables, then $$\Theta=0.$$
--
--   Role: a step of the tilted Bayes formula.
-- source:
--   Karatzas-Shreve, Brownian Motion and Stochastic Calculus, 2nd ed., Springer GTM 113 (1991), https://doi.org/10.1007/978-1-4612-0949-2, Section 3.4, Theorem 4.15; proof of Theorem 1(ii), Section EC.7.3, pp. ec27-ec43

import Mathlib
import Definitions.Def_HedgePSNV_Hedging
import Definitions.Def_HedgePSNV_Model
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace HedgePSNV

theorem subfiltration_projection_zero {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} {mF mK : ℝ≥0 → MeasurableSpace Ω}
    (hF1 : Monotone mF) (hF2 : ∀ s, mF s ≤ mΩ) (hF3 : ∀ s, Measurable[mF s] (W s))
    (hF4 : ∀ u v, u ≤ v →
      Indep (mF u) (MeasurableSpace.comap (fun ω => W v ω - W u ω) inferInstance) P)
    (hF5 : ∀ u v, MemLp (fun ω => W v ω - W u ω) 2 P)
    (hF6 : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ∂P = 0)
    (hF7 : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ^ 2 ∂P = (v : ℝ) - u)
    (hK1 : Monotone mK) (hK2 : ∀ s, mK s ≤ mΩ) (hK3 : ∀ s, Measurable[mK s] (W s))
    (hK4 : ∀ u v, u ≤ v →
      Indep (mK u) (MeasurableSpace.comap (fun ω => W v ω - W u ω) inferInstance) P)
    (hK5 : ∀ u v, MemLp (fun ω => W v ω - W u ω) 2 P)
    (hK6 : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ∂P = 0)
    (hK7 : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ^ 2 ∂P = (v : ℝ) - u)
    (hKF : ∀ s, mK s ≤ mF s) (T : ℝ≥0)
    (μ : Measure (ℝ × Ω)) (hμ : μ = (volume.restrict (Set.Ico (0 : ℝ) T)).prod P)
    (H1 : ∀ (u : ℝ≥0) (Y : Ω → ℝ), u ≤ T → Measurable[mF u] Y → (∃ C, ∀ ω, |Y ω| ≤ C) →
      condExp (mK T) P Y =ᵐ[P] condExp (mK u) P Y)
    {θ θB : Lp ℝ 2 P} {a : Lp ℝ 2 μ}
    (hr1 : θB ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 P | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧
          ∃ Y : Ω → ℝ, Measurable[mF u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun ω => Y ω * (W v ω - W u ω)) 2 P, g = h.toLp _} : Set (Lp ℝ 2 P)))
    (hr2 : a ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧
          ∃ Y : Ω → ℝ, Measurable[mF u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
            g = h.toLp _} : Set (Lp ℝ 2 μ)))
    (hr3 : ∀ u v : ℝ≥0, u ≤ v → v ≤ T → ∀ Y : Ω → ℝ, Measurable[mF u] Y →
        (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) →
        ∫ ω, (θB : Ω → ℝ) ω * (Y ω * (W v ω - W u ω)) ∂P =
          ∫ z, (a : ℝ × Ω → ℝ) z * ((Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) ∂μ)
    {c : ℝ × Ω → ℝ} (hc : MemLp c 2 μ)
    (hproj : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 μ,
      hψ.toLp ψ ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧
          ∃ Y : Ω → ℝ, Measurable[mF u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
            g = h.toLp _} : Set (Lp ℝ 2 μ)) →
      ∫ z, c z * ψ z ∂μ = ∫ z, (θ : Ω → ℝ) z.2 * ψ z ∂μ)
    {η : ℝ≥0 → Ω → ℝ} (hηa : ∀ u, Measurable[mK u] (η u)) (hηc : ∀ ω, Continuous fun v => η v ω)
    (hac : ∀ᵐ z ∂μ, a z = -(η z.1.toNNReal z.2) * c z)
    {Θ : Lp ℝ 2 P} (hΘ : (Θ : Ω → ℝ) =ᵐ[P] condExp (mK T) P θ)
    (hΘB : (Θ : Ω → ℝ) =ᵐ[P] condExp (mK T) P θB) (t : ℝ≥0)
    (hΘt : ∀ Y : Ω → ℝ, Measurable[mK t] Y → ∀ C : ℝ, (∀ ω, |Y ω| ≤ C) →
      ∫ ω, (Θ : Ω → ℝ) ω * Y ω ∂P = 0) :
    Θ = 0 := by sorry

end HedgePSNV
