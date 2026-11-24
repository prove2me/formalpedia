-- Prove2me | Theorems.Thm_GlobalTheory_PicDom_isOfFinOrder_of_not_charZero
-- name    : GlobalTheory.PicDom.isOfFinOrder_of_not_charZero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:48:29.088245+00:00
-- url     : https://prove2.me/theorems/14d40be7-8cd1-4a4d-8f95-dcb5c6bcd280
-- title:
--   Pic Dom: is Of Fin Order of not char Zero
-- statement:
--   The Pic Dom construction uses the is Of Fin Order of not char Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PicIsOfFinOrderOfFiniteInt.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PicIsOfFinOrderOfFiniteInt.lean#L16-L27

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

theorem GlobalTheory.PicDom.isOfFinOrder_of_not_charZero (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B]
    (hc : ¬ CharZero B) (M : CommRing.Pic B) : IsOfFinOrder M := by sorry
