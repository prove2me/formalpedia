-- Prove2me | Theorems.Thm_GlobalTheory_PicDom_isOfFinOrder_of_numberField
-- name    : GlobalTheory.PicDom.isOfFinOrder_of_numberField
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:48:35.394954+00:00
-- url     : https://prove2.me/theorems/37ec7240-b9cf-4afa-933c-1e1db25702e1
-- title:
--   Pic Dom: is Of Fin Order of number Field
-- statement:
--   The Pic Dom construction uses the is Of Fin Order of number Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PicIsOfFinOrderOfFiniteInt.lean#L71-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PicIsOfFinOrderOfFiniteInt.lean#L71-L121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOfFinOrderOfIsOfFinOrderMapRingHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicIsOfFinOrderOfFiniteInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.PicDom
variable (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B] [CharZero B]

theorem GlobalTheory.PicDom.isOfFinOrder_of_numberField (K : Type) [Field K] [Algebra B K] [IsFractionRing B K] [NumberField K]
    (M : CommRing.Pic B) : IsOfFinOrder M := by sorry
