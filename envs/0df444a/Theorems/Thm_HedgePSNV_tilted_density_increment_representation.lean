-- Prove2me | Theorems.Thm_HedgePSNV_tilted_density_increment_representation
-- name    : HedgePSNV.tilted_density_increment_representation
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T15:42:05.996418+00:00
-- url     : https://prove2.me/theorems/9453be9f-dfd9-4acb-8d02-afd40fab369c
-- title:
--   Integrand representation of $\zeta(Z_T-Z_t)$
-- statement:
--   For bounded $\mathcal K_t$-measurable $\zeta$ and $t\le T$, $\zeta(Z_T-Z_t)$ lies in the closed span of simple $dB$-integrals with integrand $$\zeta\,(-Z_u\eta_u)\,\mathbf 1_{[t,T)}(u),$$ and the projection identities hold.
--
--   Role: a step of the tilted Bayes formula.
-- source:
--   Karatzas-Shreve, Brownian Motion and Stochastic Calculus, 2nd ed., Springer GTM 113 (1991), https://doi.org/10.1007/978-1-4612-0949-2, Section 3.4, Theorem 4.15 (martingale representation) and Section 3.5 (5.4); proof of Theorem 1(ii), Section EC.7.3, pp. ec27-ec43

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

theorem tilted_density_increment_representation {p : HedgePSNV.Params} {Ω : Type*} [mΩ : MeasurableSpace Ω] (M : HedgePSNV.Model p Ω)
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
    {Kj : ℝ≥0 → Ω → ℝ}
    (hKj : HasBrownianItoIntegral M.P (completedBrownianPast M.P W (fun _ => 0))
      (fun s ω => W s ω 0) (fun s ω => -(Z s ω * M.η (min s p.T) ω)) Kj)
    (hKz : ∀ t, ∀ᵐ ω ∂M.P, Z t ω = 1 + Kj t ω)
    (μ : Measure (ℝ × Ω)) (hμ : μ = (volume.restrict (Set.Ico (0 : ℝ) p.T)).prod M.P)
    {mK : ℝ≥0 → MeasurableSpace Ω} (hK1 : Monotone mK) (hK2 : ∀ s, mK s ≤ mΩ)
    (hK3 : ∀ s, Measurable[mK s] (M.B s))
    (hK4 : ∀ u v, u ≤ v →
      Indep (mK u) (MeasurableSpace.comap (fun ω => M.B v ω - M.B u ω) inferInstance) M.P)
    (hK5 : ∀ u v, MemLp (fun ω => M.B v ω - M.B u ω) 2 M.P)
    (hK6 : ∀ u v, u ≤ v → ∫ ω, (M.B v ω - M.B u ω) ∂M.P = 0)
    (hK7 : ∀ u v, u ≤ v → ∫ ω, (M.B v ω - M.B u ω) ^ 2 ∂M.P = (v : ℝ) - u)
    (hZK : ∀ s, s ≤ p.T → Measurable[mK s] (Z s))
    (hηK : ∀ s, Measurable[mK s] (fun ω => M.η (min s p.T) ω))
    (hKF : ∀ s, mK s ≤ M.F s)
    (H1 : ∀ (u : ℝ≥0) (Y : Ω → ℝ), u ≤ p.T → Measurable[M.F u] Y → (∃ C, ∀ ω, |Y ω| ≤ C) →
      condExp (mK p.T) M.P Y =ᵐ[M.P] condExp (mK u) M.P Y)
    {t : ℝ≥0} (htT : t ≤ p.T) {ζ : Ω → ℝ} (hζ : Measurable[mK t] ζ) {Cz : ℝ}
    (hCz : ∀ ω, |ζ ω| ≤ Cz) :
    ∃ hc2 : MemLp (fun z : ℝ × Ω =>
        ζ z.2 * (Z (min (max z.1.toNNReal t) p.T) z.2 - Z (min t p.T) z.2)) 2 μ,
    ∃ θ2 : Lp ℝ 2 M.P, ((θ2 : Ω → ℝ) =ᵐ[M.P] fun ω => ζ ω * (Z p.T ω - Z t ω)) ∧
    ∃ a2 : Lp ℝ 2 μ,
      ((a2 : ℝ × Ω → ℝ) =ᵐ[μ] fun z => ζ z.2 *
        (-(Z z.1.toNNReal z.2 * M.η (min z.1.toNNReal p.T) z.2) *
          (1 - (Set.Ico ((0 : ℝ≥0) : ℝ) t).indicator (fun _ => (1 : ℝ)) z.1))) ∧
      (θ2 ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 M.P | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ p.T ∧
          ∃ Y : Ω → ℝ, Measurable[mK u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun ω => Y ω * (M.B v ω - M.B u ω)) 2 M.P, g = h.toLp _} : Set (Lp ℝ 2 M.P)) ∧
        a2 ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ p.T ∧
        ∃ Y : Ω → ℝ, Measurable[mK u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
        ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
          g = h.toLp _} : Set (Lp ℝ 2 μ)) ∧
        ∀ u v : ℝ≥0, u ≤ v → v ≤ p.T → ∀ Y : Ω → ℝ, Measurable[mK u] Y →
          (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) →
          ∫ ω, (θ2 : Ω → ℝ) ω * (Y ω * (M.B v ω - M.B u ω)) ∂M.P =
            ∫ z, (a2 : ℝ × Ω → ℝ) z * ((Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) ∂μ) ∧
      hc2.toLp _ ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ p.T ∧
        ∃ Y : Ω → ℝ, Measurable[mK u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
        ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
          g = h.toLp _} : Set (Lp ℝ 2 μ)) ∧
      ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 μ,
        hψ.toLp ψ ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ p.T ∧
        ∃ Y : Ω → ℝ, Measurable[mK u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
        ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
          g = h.toLp _} : Set (Lp ℝ 2 μ)) →
        ∫ z, ζ z.2 * (Z (min (max z.1.toNNReal t) p.T) z.2 - Z (min t p.T) z.2) * ψ z ∂μ =
          ∫ z, (θ2 : Ω → ℝ) z.2 * ψ z ∂μ := by sorry

end HedgePSNV
