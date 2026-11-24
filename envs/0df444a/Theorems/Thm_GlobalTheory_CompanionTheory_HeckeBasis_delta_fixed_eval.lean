-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBasis_delta_fixed_eval
-- name    : GlobalTheory.CompanionTheory.HeckeBasis.delta_fixed_eval
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:45:32.292398+00:00
-- url     : https://prove2.me/theorems/09ffd3a6-bce1-445e-b4a3-759ac0147ed2
-- title:
--   Hecke Basis: delta fixed eval
-- statement:
--   The Hecke Basis construction uses the delta fixed eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeOperatorsSpanAndFaithful.lean#L79-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeOperatorsSpanAndFaithful.lean#L79-L89

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

theorem GlobalTheory.CompanionTheory.HeckeBasis.delta_fixed_eval (h : Hk K) : IsFixed K ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K)) := by sorry
