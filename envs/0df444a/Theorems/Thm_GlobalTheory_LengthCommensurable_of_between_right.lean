-- Prove2me | Theorems.Thm_GlobalTheory_LengthCommensurable_of_between_right
-- name    : GlobalTheory.LengthCommensurable.of_between_right
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:59:12.502738+00:00
-- url     : https://prove2.me/theorems/f1b8b796-3342-4cf0-9efe-92778b53b5ef
-- title:
--   Length Commensurable: of between right
-- statement:
--   The Length Commensurable construction uses the of between right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L108-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L108-L110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
variable {A A' B B' C : Submodule R V}
open GlobalTheory.LengthCommensurable

theorem GlobalTheory.LengthCommensurable.of_between_right (h : LengthCommensurable A C) (hCB : C ≤ B) (hBA : B ≤ A) :
    LengthCommensurable B C := by sorry
