-- Prove2me | Theorems.Thm_HedgePSNV_conditional_tail_integrand_representation
-- name    : HedgePSNV.conditional_tail_integrand_representation
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T15:47:47.567841+00:00
-- url     : https://prove2.me/theorems/f9a309a7-8ef6-4f4b-99c1-29ff05249166
-- title:
--   The tail $\zeta(\theta-\mathbb E[\theta\mid\mathcal F_t])$ has integrand $\zeta a\mathbf 1_{[t,T)}$
-- statement:
--   If $\theta=\int a\,dW$ (closed-span sense), $\zeta$ is bounded $\mathcal F_t$-measurable, then $\zeta(\theta-\theta_t)$ with $\theta_t=\mathbb E[\theta\mid\mathcal F_t]$ is represented by $$\zeta\,a_u\,\mathbf 1_{[t,T)}(u).$$
--
--   Role: a step of the tilted Bayes formula.
-- source:
--   Karatzas-Shreve, Brownian Motion and Stochastic Calculus, 2nd ed., Springer GTM 113 (1991), https://doi.org/10.1007/978-1-4612-0949-2, Section 3.4, Theorem 4.15 and Section 3.2, Proposition 2.10; proof of Theorem 1(ii), Section EC.7.3, pp. ec27-ec43

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

theorem conditional_tail_integrand_representation {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} {m : ℝ≥0 → MeasurableSpace Ω}
    (hK1 : Monotone m) (hK2 : ∀ s, m s ≤ mΩ) (hK3 : ∀ s, Measurable[m s] (W s))
    (hK4 : ∀ u v, u ≤ v →
      Indep (m u) (MeasurableSpace.comap (fun ω => W v ω - W u ω) inferInstance) P)
    (hK5 : ∀ u v, MemLp (fun ω => W v ω - W u ω) 2 P)
    (hK6 : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ∂P = 0)
    (hK7 : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ^ 2 ∂P = (v : ℝ) - u)
    (T : ℝ≥0) (μ : Measure (ℝ × Ω)) (hμ : μ = (volume.restrict (Set.Ico (0 : ℝ) T)).prod P)
    {t : ℝ≥0} (htT : t ≤ T) {θ : Lp ℝ 2 P} {a : Lp ℝ 2 μ}
    (hr1 : θ ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 P | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧
          ∃ Y : Ω → ℝ, Measurable[m u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun ω => Y ω * (W v ω - W u ω)) 2 P, g = h.toLp _} : Set (Lp ℝ 2 P)))
    (hr2 : a ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧
          ∃ Y : Ω → ℝ, Measurable[m u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
            g = h.toLp _} : Set (Lp ℝ 2 μ)))
    (hr3 : ∀ u v : ℝ≥0, u ≤ v → v ≤ T → ∀ Y : Ω → ℝ, Measurable[m u] Y →
        (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) →
        ∫ ω, (θ : Ω → ℝ) ω * (Y ω * (W v ω - W u ω)) ∂P =
          ∫ z, (a : ℝ × Ω → ℝ) z * ((Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) ∂μ)
    {θt : Lp ℝ 2 P} (hθt : (θt : Ω → ℝ) =ᵐ[P] condExp (m t) P θ) {ζ : Ω → ℝ}
    (hζ : Measurable[m t] ζ) {Cz : ℝ} (hCz : ∀ ω, |ζ ω| ≤ Cz)
    {θ' : Lp ℝ 2 P} (hθ' : θ' =ᵐ[P] fun ω => ζ ω * (θ ω - θt ω))
    {b' : Lp ℝ 2 μ}
    (hb' : b' =ᵐ[μ] fun z => ζ z.2 * (a z * (1 - (Set.Ico ((0 : ℝ≥0) : ℝ) t).indicator (fun _ => (1 : ℝ)) z.1))) :
    θ' ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 P | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧
          ∃ Y : Ω → ℝ, Measurable[m u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun ω => Y ω * (W v ω - W u ω)) 2 P, g = h.toLp _} : Set (Lp ℝ 2 P)) ∧
      b' ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧
          ∃ Y : Ω → ℝ, Measurable[m u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
            g = h.toLp _} : Set (Lp ℝ 2 μ)) ∧
      ∀ u v : ℝ≥0, u ≤ v → v ≤ T → ∀ Y : Ω → ℝ, Measurable[m u] Y →
        (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) →
        ∫ ω, (θ' : Ω → ℝ) ω * (Y ω * (W v ω - W u ω)) ∂P =
          ∫ z, (b' : ℝ × Ω → ℝ) z * ((Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) ∂μ := by sorry

end HedgePSNV
