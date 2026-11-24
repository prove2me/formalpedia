-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Averaging_lintegral_sum_cosets_eq
-- name    : GlobalTheory.CompanionTheory.SW.Averaging.lintegral_sum_cosets_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:01:15.565888+00:00
-- url     : https://prove2.me/theorems/0a3a2fc4-1c10-433a-9252-83c341aaea9e
-- title:
--   Averaging: lintegral sum cosets eq
-- statement:
--   The Averaging construction uses the lintegral sum cosets eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/QuotientMeasureTower.lean#L60-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/QuotientMeasureTower.lean#L60-L128

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteCovolumeUnimodular
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ClosedSubgroupQuotientMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuotientMeasureTower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Averaging
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {G₁ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]

theorem GlobalTheory.CompanionTheory.SW.Averaging.lintegral_sum_cosets_eq (ι : G₁ →* G) (hιc : Continuous ι) (hι : Function.Injective ι)
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    (μ₁ : Measure G₁) [SFinite μ₁] [μ₁.IsMulLeftInvariant] [μ₁.IsInvInvariant]
    (Γ : Subgroup G) [Countable Γ] (Γ₁ : Subgroup G₁) [Countable Γ₁]
    (𝓕 : Set G) (𝓕₁ : Set G₁)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (h𝓕₁ : IsFundamentalDomain Γ₁ 𝓕₁ μ₁)
    (hΓ : ∀ u ∈ Γ₁, ι u ∈ Γ) {Q : Type} [Countable Q] (r : Q → G) (hr : ∀ q, r q ∈ Γ)
    (hQ : ∀ γ ∈ Γ, ∃! q, ∃ u ∈ Γ₁, γ = ι u * r q)
    (w : G → ℝ≥0∞) (hw : Measurable w) (hw1 : ∀ g, ∫⁻ u, w (ι u * g) ∂μ₁ = 1)
    (ψ : G → ℝ≥0∞) (hψ : Measurable ψ) (hinv : ∀ u ∈ Γ₁, ∀ g, ψ (ι u * g) = ψ g) :
    ∫⁻ h in 𝓕, ∑' q, ψ (r q * h) ∂μ = ∫⁻ g, w g * ∫⁻ u in 𝓕₁, ψ (ι u * g) ∂μ₁ ∂μ := by sorry
