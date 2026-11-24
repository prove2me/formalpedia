-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_exists_weight_mass_one_right_coset
-- name    : GlobalTheory.CompanionTheory.SW.exists_weight_mass_one_right_coset
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:11:51.519866+00:00
-- url     : https://prove2.me/theorems/d085fcf9-4646-42d6-bd64-ebb3a77c5d3f
-- title:
--   SW: exists weight mass one right coset
-- statement:
--   The SW construction uses the exists weight mass one right coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ClosedSubgroupQuotientMeasure.lean#L20-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ClosedSubgroupQuotientMeasure.lean#L20-L46

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_Bruhat
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ClosedSubgroupQuotientMeasure
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW

theorem GlobalTheory.CompanionTheory.SW.exists_weight_mass_one_right_coset :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* G), IsClosedEmbedding ι → ∀ (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] [μ₁.IsMulRightInvariant], ∃ w : G → ℝ≥0∞, Measurable w ∧ ∀ g, ∫⁻ u, w (ι u * g) ∂μ₁ = 1 := by sorry
