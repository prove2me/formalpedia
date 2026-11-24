-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBasis_heckeOp_delta
-- name    : GlobalTheory.CompanionTheory.HeckeBasis.heckeOp_delta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:26.009547+00:00
-- url     : https://prove2.me/theorems/c2b87b3f-e7b6-4fb6-85bf-969839b32d93
-- title:
--   Hecke Basis: hecke Op delta
-- statement:
--   The Hecke Basis construction uses the hecke Op delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeOperatorsSpanAndFaithful.lean#L144-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeOperatorsSpanAndFaithful.lean#L144-L146

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

theorem GlobalTheory.CompanionTheory.HeckeBasis.heckeOp_delta (hK : IsHeckePair K) (g : G) :
    (heckeOp hK g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) = orbitVec hK g := by sorry
