-- Prove2me | Theorems.Thm_GlobalTheory_PicDom_isOfFinOrder_of_charZero
-- name    : GlobalTheory.PicDom.isOfFinOrder_of_charZero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:48:00.847975+00:00
-- url     : https://prove2.me/theorems/f97598ce-2ce5-4269-854c-39e52c9d0c8d
-- title:
--   Pic Dom: is Of Fin Order of char Zero
-- statement:
--   The Pic Dom construction uses the is Of Fin Order of char Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PicIsOfFinOrderOfFiniteInt.lean#L123-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PicIsOfFinOrderOfFiniteInt.lean#L123-L127

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

theorem GlobalTheory.PicDom.isOfFinOrder_of_charZero (M : CommRing.Pic B) : IsOfFinOrder M := by sorry
