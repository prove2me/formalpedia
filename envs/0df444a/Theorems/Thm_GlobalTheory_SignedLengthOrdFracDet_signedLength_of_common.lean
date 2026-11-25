-- Prove2me | Theorems.Thm_GlobalTheory_SignedLengthOrdFracDet_signedLength_of_common
-- name    : GlobalTheory.SignedLengthOrdFracDet.signedLength_of_common
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:12:37.806708+00:00
-- url     : https://prove2.me/theorems/c139cc1c-0ab5-436b-887f-3973bfbe02fd
-- title:
--   Signed Length Ord Frac Det: signed Length of common
-- statement:
--   The Signed Length Ord Frac Det construction uses the signed Length of common property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthSpanEqOrdFracDet.lean#L57-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthSpanEqOrdFracDet.lean#L57-L81

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthSpanEqOrdFracDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SignedLengthOrdFracDet
open Module Submodule

theorem GlobalTheory.SignedLengthOrdFracDet.signedLength_of_common {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    {A B C : Submodule R V} (hA : C ≤ A) (hB : C ≤ B) {m n : ℕ} (hm : relLength A C = m)
    (hn : relLength B C = n) :
    LengthCommensurable A B ∧ signedLength A B = (m : ℤ) - n := by sorry
