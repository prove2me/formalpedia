-- Prove2me | Theorems.Thm_GlobalTheory_T_isOfFinOrder_pic_of_isReduced_finite_int
-- name    : GlobalTheory.T.isOfFinOrder_pic_of_isReduced_finite_int
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:36:36.864031+00:00
-- url     : https://prove2.me/theorems/6bcf05b4-6f38-422a-abc3-fef5903c71da
-- title:
--   T: is Of Fin Order pic of is Reduced finite int
-- statement:
--   The T construction uses the is Of Fin Order pic of is Reduced finite int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOfFinOrderPicOfIsReducedFiniteIntStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOfFinOrderPicOfIsReducedFiniteIntStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOfFinOrderPicOfIsReducedFiniteInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOfFinOrderPicOfIsReducedFiniteIntStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isOfFinOrder_pic_of_isReduced_finite_int : ∀ (B : Type) [CommRing B] [IsReduced B] [Module.Finite ℤ B] (M : CommRing.Pic B), IsOfFinOrder M := by sorry
