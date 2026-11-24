-- Prove2me | Theorems.Thm_GlobalTheory_CardLength_lenAt_subsingleton
-- name    : GlobalTheory.CardLength.lenAt_subsingleton
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:57.523484+00:00
-- url     : https://prove2.me/theorems/f53766ce-cbd0-4663-a2b0-785a85af359e
-- title:
--   Card Length: len At subsingleton
-- statement:
--   The Card Length construction uses the len At subsingleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogCardEqFinsumLengthLocalizedMaximal.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogCardEqFinsumLengthLocalizedMaximal.lean#L26-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogCardEqFinsumLengthLocalizedMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CardLength
variable {R : Type} [CommRing R]

theorem GlobalTheory.CardLength.lenAt_subsingleton (w : Ideal R) [w.IsPrime] (Q : Type) [AddCommGroup Q] [Module R Q]
    [Subsingleton Q] : lenAt w Q = 0 := by sorry
