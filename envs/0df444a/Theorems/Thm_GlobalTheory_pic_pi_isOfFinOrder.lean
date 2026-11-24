-- Prove2me | Theorems.Thm_GlobalTheory_pic_pi_isOfFinOrder
-- name    : GlobalTheory.pic_pi_isOfFinOrder
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:13:54.348447+00:00
-- url     : https://prove2.me/theorems/8275fd03-7798-4cf7-92f1-6a562edf7a67
-- title:
--   Global Theory: pic pi is Of Fin Order
-- statement:
--   The Global Theory construction uses the pic pi is Of Fin Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PicPiIsOfFinOrder.lean#L103-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PicPiIsOfFinOrder.lean#L103-L115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicPiIsOfFinOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory

theorem GlobalTheory.pic_pi_isOfFinOrder : ∀ (ι : Type) [Finite ι] (R : ι → Type) [∀ i, CommRing (R i)],
    (∀ i (M : CommRing.Pic (R i)), IsOfFinOrder M) →
      ∀ M : CommRing.Pic ((i : ι) → R i), IsOfFinOrder M := by sorry
