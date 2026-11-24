-- Prove2me | Theorems.Thm_GlobalTheory_HerbrandLength_loc_quot_self
-- name    : GlobalTheory.HerbrandLength.loc_quot_self
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:19:37.488944+00:00
-- url     : https://prove2.me/theorems/05692869-0ea5-4ae4-80c3-bc97997cd929
-- title:
--   Herbrand Length: loc quot self
-- statement:
--   The Herbrand Length construction uses the loc quot self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthCokerLsmulEqLengthKerAddSum.lean#L33-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthCokerLsmulEqLengthKerAddSum.lean#L33-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthEqKerAddRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HerbrandLength
open IsLocalRing
variable {A : Type} [CommRing A]

theorem GlobalTheory.HerbrandLength.loc_quot_self (p : Ideal A) [hp : p.IsPrime] :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (A ⧸ p)) = 1 := by sorry
