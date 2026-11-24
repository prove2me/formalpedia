-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Averaging_bijective_pair
-- name    : GlobalTheory.CompanionTheory.SW.Averaging.bijective_pair
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:01:15.894821+00:00
-- url     : https://prove2.me/theorems/0a38c8b6-4036-40ab-af46-ea918ed115fd
-- title:
--   Averaging: bijective pair
-- statement:
--   The Averaging construction uses the bijective pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/QuotientMeasureTower.lean#L35-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/QuotientMeasureTower.lean#L35-L58

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

theorem GlobalTheory.CompanionTheory.SW.Averaging.bijective_pair (ι : G₁ →* G) (hι : Function.Injective ι)
    (Γ : Subgroup G) (Γ₁ : Subgroup G₁) (hΓ : ∀ u ∈ Γ₁, ι u ∈ Γ)
    {Q : Type} (r : Q → G) (hr : ∀ q, r q ∈ Γ)
    (hQ : ∀ γ ∈ Γ, ∃! q, ∃ u ∈ Γ₁, γ = ι u * r q) :
    Function.Bijective (fun p : Q × Γ₁ =>
      (⟨ι (p.2 : G₁)⁻¹ * r p.1, Γ.mul_mem (hΓ _ (Γ₁.inv_mem p.2.2)) (hr p.1)⟩ : Γ)) := by sorry
