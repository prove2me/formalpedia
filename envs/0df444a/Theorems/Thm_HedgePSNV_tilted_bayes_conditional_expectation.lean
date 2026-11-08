-- Prove2me | Theorems.Thm_HedgePSNV_tilted_bayes_conditional_expectation
-- name    : HedgePSNV.tilted_bayes_conditional_expectation
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T15:13:27.073128+00:00
-- url     : https://prove2.me/theorems/7b5c408c-c311-497b-ba1f-82a1ee26c86f
-- title:
--   Bayes formula for the tilted measure $Z_T^2\,d\mathbb P$
-- statement:
--   With $Q=Z_T^2/c\,\cdot\mathbb P$ and $\theta$ the projection data of the claim, $$\mathbb E^Q\big[\theta/Z_T\mid\mathcal F_t\vee\mathcal G_T\big]=\mathbb E^Q\big[\theta/Z_T\mid\mathcal F_t\big]=\frac{\mathbb E[\theta\mid\mathcal F_t]}{Z_t}\quad Q\text{-a.s.}$$
--
--   Role: a step of the completeness argument (every square-integrable claim orthogonal to all hedgeable gains vanishes).
-- source:
--   Karatzas-Shreve, Brownian Motion and Stochastic Calculus, 2nd ed., Springer GTM 113 (1991), https://doi.org/10.1007/978-1-4612-0949-2, Section 3.5, Lemma 5.3 (Bayes rule); proof of Theorem 1(ii), Section EC.7.3, pp. ec27-ec43

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

theorem tilted_bayes_conditional_expectation {p : HedgePSNV.Params} {Ω : Type*} [mΩ : MeasurableSpace Ω] (M : HedgePSNV.Model p Ω)
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
    {θ θB : Lp ℝ 2 M.P} {a : Lp ℝ 2 μ}
    (hθB : θB ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 M.P | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ p.T ∧
      ∃ Y : Ω → ℝ, Measurable[M.F u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
      ∃ h : MemLp (fun ω => Y ω * (M.B v ω - M.B u ω)) 2 M.P, g = h.toLp _} : Set (Lp ℝ 2 M.P)))
    (ha : a ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ p.T ∧
      ∃ Y : Ω → ℝ, Measurable[M.F u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
      ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
        g = h.toLp _} : Set (Lp ℝ 2 μ)))
    (hθBa : ∀ u v : ℝ≥0, u ≤ v → v ≤ p.T → ∀ Y : Ω → ℝ, Measurable[M.F u] Y →
      (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) →
      ∫ ω, (θB : Ω → ℝ) ω * (Y ω * (M.B v ω - M.B u ω)) ∂M.P =
        ∫ z, (a : ℝ × Ω → ℝ) z * ((Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) ∂μ)
    {c : ℝ × Ω → ℝ} (hc : MemLp c 2 μ)
    (hproj : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 μ,
      hψ.toLp ψ ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ p.T ∧
        ∃ Y : Ω → ℝ, Measurable[M.F u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
        ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
          g = h.toLp _} : Set (Lp ℝ 2 μ)) →
      ∫ z, c z * ψ z ∂μ = ∫ z, (θ : Ω → ℝ) z.2 * ψ z ∂μ)
    (hac : ∀ᵐ z ∂μ, a z = -(M.η (min z.1.toNNReal p.T) z.2) * c z)
    {t : ℝ≥0} (htT : t ≤ p.T)
    (hperp : condExp (M.F t ⊔ M.G p.T) M.P (fun ω => (θ : Ω → ℝ) ω - (θB : Ω → ℝ) ω) =ᵐ[M.P]
      condExp (M.F t) M.P (fun ω => (θ : Ω → ℝ) ω - (θB : Ω → ℝ) ω)) {cc : ℝ} (hcc : 0 < cc)
    (Q : Measure Ω) (hQ : Q = M.P.withDensity fun ω => ENNReal.ofReal (M.Z p.T ω ^ 2 / cc))
    [IsFiniteMeasure Q] :
    condExp (M.F t ⊔ M.G p.T) Q (fun ω => (θ : Ω → ℝ) ω / M.Z p.T ω) =ᵐ[Q]
      (fun ω => condExp (M.F t) M.P θ ω / Z t ω) ∧
    condExp (M.F t) Q (fun ω => (θ : Ω → ℝ) ω / M.Z p.T ω) =ᵐ[Q]
      (fun ω => condExp (M.F t) M.P θ ω / Z t ω) := by sorry

end HedgePSNV
