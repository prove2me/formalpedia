-- Prove2me | Theorems.Thm_GlobalTheory_DCIndex_card_quot_eq_index
-- name    : GlobalTheory.DCIndex.card_quot_eq_index
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:34:20.316681+00:00
-- url     : https://prove2.me/theorems/08dd7959-1ce4-4e80-8fa4-16094deb46bb
-- title:
--   DCIndex: card quot eq index
-- statement:
--   The DCIndex construction uses the card quot eq index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetCardDivCardInfCommutativeSubgroup.lean#L17-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetCardDivCardInfCommutativeSubgroup.lean#L17-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetCardDivCardInfCommutativeSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
open GlobalTheory GlobalTheory.DCIndex
variable {A : Type} [Group A]

theorem GlobalTheory.DCIndex.card_quot_eq_index (hc : ∀ a b : A, a * b = b * a) (P V : Subgroup A) :
    Nat.card (DoubleCoset.Quotient (P : Set A) (V : Set A)) = (P ⊔ V).index := by sorry
