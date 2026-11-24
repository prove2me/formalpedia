-- Prove2me | Theorems.Thm_GlobalTheory_PicReducedTors_pic_isOfFinOrder
-- name    : GlobalTheory.PicReducedTors.pic_isOfFinOrder
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:44:34.906531+00:00
-- url     : https://prove2.me/theorems/d6a817e3-d8eb-4d8c-b335-1857a15f3881
-- title:
--   Pic Reduced Tors: pic is Of Fin Order
-- statement:
--   The Pic Reduced Tors construction uses the pic is Of Fin Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOfFinOrderPicOfIsReducedFiniteInt.lean#L9-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOfFinOrderPicOfIsReducedFiniteInt.lean#L9-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOfFinOrderOfIsOfFinOrderMapRingHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicIsOfFinOrderOfFiniteIntStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNatMulMemRangePiQuotientMinimalPrimesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicPiIsOfFinOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOfFinOrderPicOfIsReducedFiniteInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PicReducedTors

theorem GlobalTheory.PicReducedTors.pic_isOfFinOrder : ∀ (B : Type) [CommRing B] [IsReduced B] [Module.Finite ℤ B] (M : CommRing.Pic B),
    IsOfFinOrder M := by sorry
