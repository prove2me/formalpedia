-- Prove2me | Theorems.Thm_HedgePSNV_bounded_integrand_ito_representation
-- name    : HedgePSNV.bounded_integrand_ito_representation
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T15:58:20.775792+00:00
-- url     : https://prove2.me/theorems/ac702916-eef4-430d-8fa1-ccbe0e4ae08b
-- title:
--   A bounded integrand's Itô integral lies in the closed span of simple integrals
-- statement:
--   If $|H|\le D$ is jointly measurable and $J=\int H\,dW^0$, then $J_T$ has an $L^2$ representative $\theta$ in the closed span of $Y(B_v-B_u)$, $H$ is in the closure of simple integrands, and $$\mathbb E[\theta\,Y(B_v-B_u)]=\mathbb E\int_u^vH_s Y\,ds.$$
--
--   Role: a step of the terminal representation of $Z_T-1$.
-- source:
--   Karatzas-Shreve, Brownian Motion and Stochastic Calculus, 2nd ed., Springer GTM 113 (1991), https://doi.org/10.1007/978-1-4612-0949-2, Section 3.2, Lemma 2.4 and Proposition 2.10; proof of Theorem 1(ii), Section EC.7.3, pp. ec27-ec43

import Mathlib
import Definitions.Def_HedgePSNV_Hedging
import Definitions.Def_HedgePSNV_Model
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

set_option autoImplicit false

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped NNReal
open Classical

namespace HedgePSNV

theorem bounded_integrand_ito_representation {p : HedgePSNV.Params} {Ω : Type*} [mΩ : MeasurableSpace Ω] (M : HedgePSNV.Model p Ω)
    (hM : M.Standing) [IsProbabilityMeasure M.P] (W : ℝ≥0 → Ω → SDEState 2)
    (hW : ∀ t ω, W t ω = WithLp.toLp 2
      ![if ω ∈ toMeasurable M.P {ω | ¬ (Continuous (fun t => M.B t ω) ∧ Continuous (fun t => M.Bt t ω))}
          then 0 else M.B t ω,
        if ω ∈ toMeasurable M.P {ω | ¬ (Continuous (fun t => M.B t ω) ∧ Continuous (fun t => M.Bt t ω))}
          then 0 else M.Bt t ω])
    {H J : ℝ≥0 → Ω → ℝ} {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ u ω, |H u ω| ≤ D) (hHm : Measurable (fun z : ℝ × Ω => H z.1.toNNReal z.2))
    (hJ : HasBrownianItoIntegral M.P (completedBrownianPast M.P W (fun _ => 0))
      (fun s ω => W s ω 0) H J) (T : ℝ≥0)
    (μ : Measure (ℝ × Ω)) (hμ : μ = (volume.restrict (Set.Ico (0 : ℝ) T)).prod M.P)
    (hH2 : MemLp (fun z : ℝ × Ω => H z.1.toNNReal z.2) 2 μ) :
    ∃ θ : Lp ℝ 2 M.P, (θ : Ω → ℝ) =ᵐ[M.P] J T ∧
      (θ ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 M.P | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧
          ∃ Y : Ω → ℝ, Measurable[M.F u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun ω => Y ω * (M.B v ω - M.B u ω)) 2 M.P, g = h.toLp _} : Set (Lp ℝ 2 M.P)) ∧
      hH2.toLp _ ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧
          ∃ Y : Ω → ℝ, Measurable[M.F u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
            g = h.toLp _} : Set (Lp ℝ 2 μ)) ∧
      ∀ u v : ℝ≥0, u ≤ v → v ≤ T → ∀ Y : Ω → ℝ, Measurable[M.F u] Y →
        (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) →
        ∫ ω, (θ : Ω → ℝ) ω * (Y ω * (M.B v ω - M.B u ω)) ∂M.P =
          ∫ z, (hH2.toLp _ : ℝ × Ω → ℝ) z * ((Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) ∂μ) := by sorry

end HedgePSNV
