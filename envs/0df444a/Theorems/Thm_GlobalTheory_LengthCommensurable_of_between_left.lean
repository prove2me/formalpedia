-- Prove2me | Theorems.Thm_GlobalTheory_LengthCommensurable_of_between_left
-- name    : GlobalTheory.LengthCommensurable.of_between_left
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:58:53.87241+00:00
-- url     : https://prove2.me/theorems/099703e1-6738-46e0-9077-c1d1a1efb6f4
-- title:
--   Length Commensurable: of between left
-- statement:
--   The Length Commensurable construction uses the of between left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L104-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L104-L106

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

theorem GlobalTheory.LengthCommensurable.of_between_left (h : LengthCommensurable A C) (hCB : C ≤ B) (hBA : B ≤ A) :
    LengthCommensurable A B := by sorry
