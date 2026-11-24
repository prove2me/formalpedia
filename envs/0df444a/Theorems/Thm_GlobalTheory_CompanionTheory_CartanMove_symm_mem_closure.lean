-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartanMove_symm_mem_closure
-- name    : GlobalTheory.CompanionTheory.CartanMove.symm_mem_closure
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:27:04.971449+00:00
-- url     : https://prove2.me/theorems/b5917623-8d6f-4c24-ba1c-33d372b882a5
-- title:
--   Cartan Move: symm mem closure
-- statement:
--   The Cartan Move construction uses the symm mem closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MovingStatement.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MovingStatement.lean#L23-L27

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

theorem GlobalTheory.CompanionTheory.CartanMove.symm_mem_closure (e : G ≃* G') {l : ℕ} (t' : Fin l → G') {s : G'}
    (hs : s ∈ Submonoid.closure (Set.range t')) :
    e.symm s ∈ Submonoid.closure (Set.range fun j => e.symm (t' j)) := by sorry
