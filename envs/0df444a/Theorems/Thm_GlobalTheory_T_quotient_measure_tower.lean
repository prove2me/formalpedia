-- Prove2me | Theorems.Thm_GlobalTheory_T_quotient_measure_tower
-- name    : GlobalTheory.T.quotient_measure_tower
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:38.679699+00:00
-- url     : https://prove2.me/theorems/aa567ba8-a710-582d-a1c1-72037f1d4aea
-- title:
--   T: quotient measure tower
-- statement:
--   The T construction uses the quotient measure tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/QuotientMeasureTowerStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/QuotientMeasureTowerStatement.lean#L6-L7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuotientMeasureTower
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuotientMeasureTowerStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.quotient_measure_tower : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* G), IsClosedEmbedding ι → ∀ (μ : Measure G) [μ.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (Γ₁ : Subgroup G₁) [Countable Γ₁] (𝓕 : Set G) (𝓕₁ : Set G₁), IsFundamentalDomain Γ 𝓕 μ → IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → (∀ u ∈ Γ₁, ι u ∈ Γ) → ∀ (Q : Type) [Countable Q] (r : Q → G), (∀ q, r q ∈ Γ) → (∀ γ ∈ Γ, ∃! q, ∃ u ∈ Γ₁, γ = ι u * r q) → ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ u ∈ Γ₁, ∀ g, φ (ι u * g) = φ g) → ∫⁻ h in 𝓕, ∑' q, φ (r q * h) ∂μ = ∫⁻ h in 𝓕, ∑' q, (μ₁ 𝓕₁)⁻¹ * ∫⁻ u in 𝓕₁, φ (ι u * (r q * h)) ∂μ₁ ∂μ := by sorry
