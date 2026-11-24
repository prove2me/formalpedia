-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBasis_IsFixed_apply_of_mem_orbit
-- name    : GlobalTheory.CompanionTheory.HeckeBasis.IsFixed.apply_of_mem_orbit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:45:26.649889+00:00
-- url     : https://prove2.me/theorems/1d9877de-86e4-4c75-ab55-a156479e2a9f
-- title:
--   Is Fixed: apply of mem orbit
-- statement:
--   The Is Fixed construction uses the apply of mem orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeOperatorsSpanAndFaithful.lean#L134-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeOperatorsSpanAndFaithful.lean#L134-L139

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeBasis
variable {G : Type} [Group G] (K : Subgroup G)
variable {K}
variable (K)
variable {K}
variable (K)
variable {K}

theorem GlobalTheory.CompanionTheory.HeckeBasis.IsFixed.apply_of_mem_orbit {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) {x z : G ⧸ K}
    (hz : z ∈ MulAction.orbit K x) : u z = u x := by sorry
