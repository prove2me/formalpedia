-- Prove2me | Theorems.Thm_GlobalTheory_LengthCommensurable_inf_right
-- name    : GlobalTheory.LengthCommensurable.inf_right
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:59:06.218327+00:00
-- url     : https://prove2.me/theorems/abc73724-fa12-416f-959e-8fcbc568c2b2
-- title:
--   Length Commensurable: inf right
-- statement:
--   The Length Commensurable construction uses the inf right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L112-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L112-L115

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

theorem GlobalTheory.LengthCommensurable.inf_right (hAB : LengthCommensurable A B) (hAC : LengthCommensurable A C) :
    LengthCommensurable A (B ⊓ C) := by sorry
