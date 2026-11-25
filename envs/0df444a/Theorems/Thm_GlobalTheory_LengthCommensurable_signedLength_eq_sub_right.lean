-- Prove2me | Theorems.Thm_GlobalTheory_LengthCommensurable_signedLength_eq_sub_right
-- name    : GlobalTheory.LengthCommensurable.signedLength_eq_sub_right
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:13:32.997335+00:00
-- url     : https://prove2.me/theorems/9140f71f-74f8-4ee4-b52a-275849a5e9da
-- title:
--   Length Commensurable: signed Length eq sub right
-- statement:
--   The Length Commensurable construction uses the signed Length eq sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L183-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L183-L185

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

theorem GlobalTheory.LengthCommensurable.signedLength_eq_sub_right (hAC : LengthCommensurable A C) (hBC : LengthCommensurable B C) :
    signedLength A B = signedLength A C - signedLength B C := by sorry
