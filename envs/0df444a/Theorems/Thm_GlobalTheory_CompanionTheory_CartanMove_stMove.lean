-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartanMove_stMove
-- name    : GlobalTheory.CompanionTheory.CartanMove.stMove
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:27:42.120271+00:00
-- url     : https://prove2.me/theorems/395b438e-0804-44d4-b210-688b20eda568
-- title:
--   Cartan Move: st Move
-- statement:
--   The Cartan Move construction uses the st Move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MovingStatement.lean#L51-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MovingStatement.lean#L51-L64

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

theorem GlobalTheory.CompanionTheory.CartanMove.stMove : StMove := by sorry
