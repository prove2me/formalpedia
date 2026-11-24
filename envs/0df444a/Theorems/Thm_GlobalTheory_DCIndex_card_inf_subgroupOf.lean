-- Prove2me | Theorems.Thm_GlobalTheory_DCIndex_card_inf_subgroupOf
-- name    : GlobalTheory.DCIndex.card_inf_subgroupOf
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:34:27.525704+00:00
-- url     : https://prove2.me/theorems/94116c72-d760-46c6-86c9-91bd2533a0d5
-- title:
--   DCIndex: card inf subgroup Of
-- statement:
--   The DCIndex construction uses the card inf subgroup Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetCardDivCardInfCommutativeSubgroup.lean#L74-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetCardDivCardInfCommutativeSubgroup.lean#L74-L79

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

theorem GlobalTheory.DCIndex.card_inf_subgroupOf {G : Type} [Group G] (T H U : Subgroup G) (hUT : U ≤ T) :
    Nat.card (H.subgroupOf T ⊓ U.subgroupOf T : Subgroup T) = Nat.card (H ⊓ U : Subgroup G) := by sorry
