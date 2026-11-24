-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_comp_inl_mem
-- name    : GlobalTheory.CompanionTheory.Ar.Giv.ResProj.comp_inl_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:21:20.043544+00:00
-- url     : https://prove2.me/theorems/ee873b80-caf2-4689-bfc6-4a18d78ecf1a
-- title:
--   Res Proj: comp inl mem
-- statement:
--   The Res Proj construction uses the comp inl mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MultihomogeneousNonvanishingOnJoin.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MultihomogeneousNonvanishingOnJoin.lean#L40-L44

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MultihomogeneousNonvanishingOnJoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Giv
open GlobalTheory.CompanionTheory.Ar.Giv.ResProj
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]

theorem GlobalTheory.CompanionTheory.Ar.Giv.ResProj.comp_inl_mem {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω)
    {z : (Σ k, joinIdx ι ι₂ k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (joinVec y y₂))) :
    z ∘ joinInl ι ι₂ ∈ mcPts (mCoordIdeal y) := by sorry
