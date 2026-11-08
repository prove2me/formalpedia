-- Prove2me | Theorems.Thm_HedgePSNV_stopped_integrand_representation
-- name    : HedgePSNV.stopped_integrand_representation
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T16:07:17.679399+00:00
-- url     : https://prove2.me/theorems/0843a679-9607-4c59-a36f-21b97e4a5c0c
-- title:
--   Stopping an $L^2$ integral representation
-- statement:
--   If $\theta=\int a\,dW$ in the closed-span sense and $\tau\le T$ is a stopping time, the integrand $\mathbf 1_{\{u\ge\tau\}}a_u$ represents some $\delta$ in the closed span, and $$\mathbb E\big[\delta\,\xi\,\mathbf 1_{\{u<\tau\}}\big]=0$$ for bounded $\mathcal F_u$-measurable $\xi$.
--
--   Role: a localisation step (used for the terminal representation of $Z_T-1$ and the subfiltration projection).
-- source:
--   Karatzas-Shreve, Brownian Motion and Stochastic Calculus, 2nd ed., Springer GTM 113 (1991), https://doi.org/10.1007/978-1-4612-0949-2, Section 3.2, Proposition 2.10 and Problem 2.18 (stopped integrals); proof of Theorem 1(ii), Section EC.7.3, pp. ec27-ec43

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

theorem stopped_integrand_representation {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} {m : ℝ≥0 → MeasurableSpace Ω}
    (hK1 : Monotone m) (hK2 : ∀ s, m s ≤ mΩ) (hK3 : ∀ s, Measurable[m s] (W s))
    (hK4 : ∀ u v, u ≤ v →
      Indep (m u) (MeasurableSpace.comap (fun ω => W v ω - W u ω) inferInstance) P)
    (hK5 : ∀ u v, MemLp (fun ω => W v ω - W u ω) 2 P)
    (hK6 : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ∂P = 0)
    (hK7 : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ^ 2 ∂P = (v : ℝ) - u)
    (T : ℝ≥0) (μ : Measure (ℝ × Ω)) (hμ : μ = (volume.restrict (Set.Ico (0 : ℝ) T)).prod P)
    {θ : Lp ℝ 2 P} {a : Lp ℝ 2 μ}
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
    {τ : Ω → ℝ≥0} (hτT : ∀ ω, τ ω ≤ T)
    (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s}) {bc : Lp ℝ 2 μ}
    (hbc : bc =ᵐ[μ] fun z => (if (τ z.2 : ℝ) ≤ z.1 then (1 : ℝ) else 0) * a z) :
    ∃ δ : Lp ℝ 2 P, (δ ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 P | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧
          ∃ Y : Ω → ℝ, Measurable[m u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun ω => Y ω * (W v ω - W u ω)) 2 P, g = h.toLp _} : Set (Lp ℝ 2 P)) ∧
      bc ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧
          ∃ Y : Ω → ℝ, Measurable[m u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
            g = h.toLp _} : Set (Lp ℝ 2 μ)) ∧
      ∀ u v : ℝ≥0, u ≤ v → v ≤ T → ∀ Y : Ω → ℝ, Measurable[m u] Y →
        (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) →
        ∫ ω, (δ : Ω → ℝ) ω * (Y ω * (W v ω - W u ω)) ∂P =
          ∫ z, (bc : ℝ × Ω → ℝ) z * ((Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) ∂μ) ∧
      ∀ (u : ℝ≥0) (ξ : Ω → ℝ), Measurable[m u] ξ → ∀ C : ℝ,
        (∀ ω, |ξ ω| ≤ C) → ∫ ω, δ ω * (ξ ω * (if u < τ ω then (1 : ℝ) else 0)) ∂P = 0 := by sorry

end HedgePSNV
