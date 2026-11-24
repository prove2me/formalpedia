-- Prove2me | Theorems.Thm_GlobalTheory_pic_isOfFinOrder_of_finite_int
-- name    : GlobalTheory.pic_isOfFinOrder_of_finite_int
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:13:37.091957+00:00
-- url     : https://prove2.me/theorems/92bfa94e-f30e-4417-82ae-7b638abedb3a
-- title:
--   Global Theory: pic is Of Fin Order of finite int
-- statement:
--   The Global Theory construction uses the pic is Of Fin Order of finite int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PicIsOfFinOrderOfFiniteInt.lean#L131-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PicIsOfFinOrderOfFiniteInt.lean#L131-L136

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

theorem GlobalTheory.pic_isOfFinOrder_of_finite_int : ∀ (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B]
    (M : CommRing.Pic B), IsOfFinOrder M := by sorry
