-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartanMove_isCartan_comap
-- name    : GlobalTheory.CompanionTheory.CartanMove.isCartan_comap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:27:04.589807+00:00
-- url     : https://prove2.me/theorems/562c0282-eb17-4132-949c-0f49e7befb88
-- title:
--   Cartan Move: is Cartan comap
-- statement:
--   The Cartan Move construction uses the is Cartan comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MovingStatement.lean#L29-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MovingStatement.lean#L29-L49

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MovingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.Fl
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartanMove
variable {G G' : Type} [Group G] [Group G']

theorem GlobalTheory.CompanionTheory.CartanMove.isCartan_comap (e : G ≃* G') {K' : Subgroup G'} {d l : ℕ} (h : IsCartan K' d l) :
    IsCartan (K'.comap e.toMonoidHom) d l := by sorry
