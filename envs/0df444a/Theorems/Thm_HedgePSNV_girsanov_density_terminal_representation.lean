-- Prove2me | Theorems.Thm_HedgePSNV_girsanov_density_terminal_representation
-- name    : HedgePSNV.girsanov_density_terminal_representation
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T15:53:44.084757+00:00
-- url     : https://prove2.me/theorems/c186350b-73df-4cb1-899d-546dfed58780
-- title:
--   $Z_T-1$ is the $L^2$ limit of simple $dB$-integrals with integrand $-Z\eta$
-- statement:
--   $Z_T-1$ lies in the closed span of simple $dB$-integrals, its integrand $-Z_u\eta_u$ lies in the closure of simple integrands in $L^2(dt\otimes\mathbb P)$, and $$\mathbb E[(Z_T-1)\,Y(B_v-B_u)]=\mathbb E\int_u^v(-Z_s\eta_s)Y\,ds.$$
--
--   Role: a step of the tilted Bayes formula.
-- source:
--   Karatzas-Shreve, Brownian Motion and Stochastic Calculus, 2nd ed., Springer GTM 113 (1991), https://doi.org/10.1007/978-1-4612-0949-2, Section 3.2, Propositions 2.6 and 2.10 (approximation by simple processes; isometry); proof of Theorem 1(ii), Section EC.7.3, pp. ec27-ec43

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

theorem girsanov_density_terminal_representation {p : HedgePSNV.Params} {Ω : Type*} [mΩ : MeasurableSpace Ω] (M : HedgePSNV.Model p Ω)
    (hM : M.Standing) [IsProbabilityMeasure M.P] (h5 : M.Assumption5) (W : ℝ≥0 → Ω → SDEState 2)
    (hW : ∀ t ω, W t ω = WithLp.toLp 2
      ![if ω ∈ toMeasurable M.P {ω | ¬ (Continuous (fun t => M.B t ω) ∧ Continuous (fun t => M.Bt t ω))}
          then 0 else M.B t ω,
        if ω ∈ toMeasurable M.P {ω | ¬ (Continuous (fun t => M.B t ω) ∧ Continuous (fun t => M.Bt t ω))}
          then 0 else M.Bt t ω])
    (hC : ∀ H : ℝ≥0 → Ω → ℝ,
      (∀ s, Measurable[completedBrownianPast M.P W (fun _ => 0) s] (H s)) →
      (∀ s, Measurable (H s)) → (∀ ω, Continuous fun s => H s ω) →
      ∀ C : ℝ, (∀ s ω, |H s ω| ≤ C) →
      ∃ Jc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Jc t ω) ∧
        (∀ t, Measurable[completedBrownianPast M.P W (fun _ => 0) t] (Jc t)) ∧
        (∀ t, Measurable (Jc t)) ∧ (∀ ω, Jc 0 ω = 0) ∧
        HasBrownianItoIntegral M.P (completedBrownianPast M.P W (fun _ => 0))
          (fun s ω => W s ω 0) H Jc)
    {Ic : ℝ≥0 → Ω → ℝ} (hIc : ∀ ω, Continuous fun t => Ic t ω)
    (hIa : ∀ t, Measurable[completedBrownianPast M.P W (fun _ => 0) t] (Ic t))
    (hIm : ∀ t, Measurable (Ic t)) (hI0 : ∀ ω, Ic 0 ω = 0)
    (hIe : ∀ t, t ≤ p.T → Ic t =ᵐ[M.P] M.I t) (Z : ℝ≥0 → Ω → ℝ)
    (hZ : ∀ s ω, Z s ω =
      Real.exp (-(Ic s ω) - (1 / 2) * ∫ u in (0 : ℝ)..s.val, M.η (min u.toNNReal p.T) ω ^ 2))
    {K : ℝ≥0 → Ω → ℝ}
    (hK : HasBrownianItoIntegral M.P (completedBrownianPast M.P W (fun _ => 0))
      (fun s ω => W s ω 0) (fun s ω => -(Z s ω * M.η (min s p.T) ω)) K)
    (hKz : ∀ t, ∀ᵐ ω ∂M.P, Z t ω = 1 + K t ω)
    (μ : Measure (ℝ × Ω)) (hμ : μ = (volume.restrict (Set.Ico (0 : ℝ) p.T)).prod M.P) :
    ∃ hf2 : MemLp (fun z : ℝ × Ω => -(Z z.1.toNNReal z.2 * M.η (min z.1.toNNReal p.T) z.2)) 2 μ,
      ∃ θ : Lp ℝ 2 M.P, (θ : Ω → ℝ) =ᵐ[M.P] (fun ω => Z p.T ω - 1) ∧
      (θ ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 M.P | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ p.T ∧
          ∃ Y : Ω → ℝ, Measurable[M.F u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun ω => Y ω * (M.B v ω - M.B u ω)) 2 M.P, g = h.toLp _} : Set (Lp ℝ 2 M.P)) ∧
      hf2.toLp _ ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ p.T ∧
          ∃ Y : Ω → ℝ, Measurable[M.F u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
            g = h.toLp _} : Set (Lp ℝ 2 μ)) ∧
      ∀ u v : ℝ≥0, u ≤ v → v ≤ p.T → ∀ Y : Ω → ℝ, Measurable[M.F u] Y →
        (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) →
        ∫ ω, (θ : Ω → ℝ) ω * (Y ω * (M.B v ω - M.B u ω)) ∂M.P =
          ∫ z, (hf2.toLp _ : ℝ × Ω → ℝ) z * ((Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) ∂μ) := by sorry

end HedgePSNV
