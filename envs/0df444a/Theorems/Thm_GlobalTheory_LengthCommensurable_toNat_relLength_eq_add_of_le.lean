-- Prove2me | Theorems.Thm_GlobalTheory_LengthCommensurable_toNat_relLength_eq_add_of_le
-- name    : GlobalTheory.LengthCommensurable.toNat_relLength_eq_add_of_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:58:47.229264+00:00
-- url     : https://prove2.me/theorems/74f54b4d-1c90-4e97-87e2-7cc31007668d
-- title:
--   Length Commensurable: to Nat rel Length eq add of le
-- statement:
--   The Length Commensurable construction uses the to Nat rel Length eq add of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L151-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L151-L154

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

theorem GlobalTheory.LengthCommensurable.toNat_relLength_eq_add_of_le (h : LengthCommensurable A C) (hCB : C ≤ B) (hBA : B ≤ A) :
    (relLength A C).toNat = (relLength A B).toNat + (relLength B C).toNat := by sorry
