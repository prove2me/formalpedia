-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Averaging_setLIntegral_mul_right_eq
-- name    : GlobalTheory.CompanionTheory.SW.Averaging.setLIntegral_mul_right_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:56.475321+00:00
-- url     : https://prove2.me/theorems/f9ebc0d5-d2f3-4408-8fa1-8d7e135f4868
-- title:
--   Averaging: set LIntegral mul right eq
-- statement:
--   The Averaging construction uses the set LIntegral mul right eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/QuotientMeasureTower.lean#L16-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/QuotientMeasureTower.lean#L16-L33

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

theorem GlobalTheory.CompanionTheory.SW.Averaging.setLIntegral_mul_right_eq (μ₁ : Measure G₁) [SFinite μ₁] [μ₁.IsMulLeftInvariant]
    [μ₁.IsMulRightInvariant] (Γ₁ : Subgroup G₁) [Countable Γ₁] (𝓕₁ : Set G₁)
    (h𝓕₁ : IsFundamentalDomain Γ₁ 𝓕₁ μ₁) (f : G₁ → ℝ≥0∞)
    (hf : ∀ γ ∈ Γ₁, ∀ u, f (γ * u) = f u) (u₀ : G₁) :
    ∫⁻ u in 𝓕₁, f (u * u₀) ∂μ₁ = ∫⁻ u in 𝓕₁, f u ∂μ₁ := by sorry
