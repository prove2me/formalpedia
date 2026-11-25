-- Prove2me | Theorems.Thm_GlobalTheory_LengthCommensurable_signedLength_eq_toNat_sub_of_ge
-- name    : GlobalTheory.LengthCommensurable.signedLength_eq_toNat_sub_of_ge
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:15.484739+00:00
-- url     : https://prove2.me/theorems/e0bbee4a-d28c-4960-926b-a0f2679181ef
-- title:
--   Length Commensurable: signed Length eq to Nat sub of ge
-- statement:
--   The Length Commensurable construction uses the signed Length eq to Nat sub of ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L191-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean#L191-L195

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

theorem GlobalTheory.LengthCommensurable.signedLength_eq_toNat_sub_of_ge {D : Submodule R V} (h : LengthCommensurable A B)
    (hDA : LengthCommensurable D A) (hAD : A ≤ D) (hBD : B ≤ D) :
    signedLength A B = ((relLength D B).toNat : ℤ) - ((relLength D A).toNat : ℤ) := by sorry
