-- Prove2me | Theorems.Thm_GlobalTheory_LengthCommensurable_sup_right
-- name    : GlobalTheory.LengthCommensurable.sup_right
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:58:38.202066+00:00
-- url     : https://prove2.me/theorems/0e72f515-e7d8-4271-b8ef-242d9b9c1fe0
-- title:
--   Length Commensurable: sup right
-- statement:
--   The Length Commensurable construction uses the sup right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L117-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L117-L120

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

theorem GlobalTheory.LengthCommensurable.sup_right (hAB : LengthCommensurable A B) (hAC : LengthCommensurable A C) :
    LengthCommensurable A (B ⊔ C) := by sorry
