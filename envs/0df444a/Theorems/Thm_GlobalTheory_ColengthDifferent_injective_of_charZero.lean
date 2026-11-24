-- Prove2me | Theorems.Thm_GlobalTheory_ColengthDifferent_injective_of_charZero
-- name    : GlobalTheory.ColengthDifferent.injective_of_charZero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:14:33.365814+00:00
-- url     : https://prove2.me/theorems/8f263924-1be0-496d-b1f4-38afd8afe940
-- title:
--   Colength Different: injective of char Zero
-- statement:
--   The Colength Different construction uses the injective of char Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColengthDvdOfNeZero.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColengthDvdOfNeZero.lean#L11-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColengthDvdOfNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.ColengthDifferent
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.ColengthDifferent.injective_of_charZero {F : Type} [Field F] [CharZero F] (f : 𝓞 E →+* F) :
    Function.Injective f := by sorry
