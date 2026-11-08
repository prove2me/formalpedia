-- Prove2me | Theorems.Thm_HedgePSNV_orthogonal_claim_integrand_relation
-- name    : HedgePSNV.orthogonal_claim_integrand_relation
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T15:07:52.579197+00:00
-- url     : https://prove2.me/theorems/f79d41b6-c68d-4ac8-ad70-5a63ab4e60e4
-- title:
--   Orthogonality to admissible gains links the claim's $dB$-integrand to its projection
-- statement:
--   If $f\in L^2$ has $dB$-integrand $a$ and is orthogonal to every admissible gains $\chi_T$, there are $a',c\in L^2(dt\otimes\mathbb P)$ (with $a'$ in the closure of simple integrands and $c$ the projection of $f$) with $$a'X\sigma+cX\mu=0\quad dt\otimes\mathbb P\text{-a.e.}$$
--
--   Role: a step of the completeness argument (every square-integrable claim orthogonal to all hedgeable gains vanishes).
-- source:
--   Wang-Yao-Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, https://arxiv.org/abs/2201.01026v4, Section 3.2 (admissible strategies); proof of Theorem 1(ii), Section EC.7.3, pp. ec27-ec43

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

theorem orthogonal_claim_integrand_relation {p : HedgePSNV.Params} {Ω : Type*} [mΩ : MeasurableSpace Ω] (M : HedgePSNV.Model p Ω)
    (hM : M.Standing) [IsProbabilityMeasure M.P] (h4 : M.Assumption4)
    (μ : Measure (ℝ × Ω)) (hμ : μ = (volume.restrict (Set.Ico (0 : ℝ) p.T)).prod M.P)
    {f : Ω → ℝ} (hf : MemLp f 2 M.P) {a : ℝ × Ω → ℝ} (ha2 : MemLp a 2 μ)
    (ha : ∀ u v : ℝ≥0, u ≤ v → v ≤ p.T → ∀ Y : Ω → ℝ, Measurable[M.F u] Y →
      (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) →
      ∫ ω, f ω * (Y ω * (M.B v ω - M.B u ω)) ∂M.P =
        ∫ z, a z * ((Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) ∂μ)
    (hfA : ∀ θχ ∈ M.AX, ∫ ω, f ω * θχ.2 p.T ω ∂M.P = 0) :
    ∃ a' c : ℝ × Ω → ℝ, MemLp a' 2 μ ∧ MemLp c 2 μ ∧
      (∀ h : MemLp a' 2 μ,
        h.toLp a' ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ p.T ∧
          ∃ Y : Ω → ℝ, Measurable[M.F u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
            g = h.toLp _} : Set (Lp ℝ 2 μ))) ∧
      (∀ u v : ℝ≥0, u ≤ v → v ≤ p.T → ∀ Y : Ω → ℝ, Measurable[M.F u] Y →
        (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) →
        ∫ ω, f ω * (Y ω * (M.B v ω - M.B u ω)) ∂M.P =
          ∫ z, a' z * ((Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) ∂μ) ∧
      (∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 μ,
        hψ.toLp ψ ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ p.T ∧
          ∃ Y : Ω → ℝ, Measurable[M.F u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
            g = h.toLp _} : Set (Lp ℝ 2 μ)) →
        ∫ z, c z * ψ z ∂μ = ∫ z, f z.2 * ψ z ∂μ) ∧
      ∀ᵐ z ∂μ, a' z * (M.X z.1.toNNReal z.2 * M.σ z.1.toNNReal z.2) +
        c z * (M.X z.1.toNNReal z.2 * M.μ z.1.toNNReal z.2) = 0 := by sorry

end HedgePSNV
