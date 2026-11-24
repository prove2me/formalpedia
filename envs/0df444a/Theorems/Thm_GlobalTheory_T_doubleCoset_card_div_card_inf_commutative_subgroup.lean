-- Prove2me | Theorems.Thm_GlobalTheory_T_doubleCoset_card_div_card_inf_commutative_subgroup
-- name    : GlobalTheory.T.doubleCoset_card_div_card_inf_commutative_subgroup
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:32:47.168269+00:00
-- url     : https://prove2.me/theorems/706998e0-547d-4e66-94e2-0a8c4adc4331
-- title:
--   T: double Coset card div card inf commutative subgroup
-- statement:
--   The T construction uses the double Coset card div card inf commutative subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetCardDivCardInfCommutativeSubgroupStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetCardDivCardInfCommutativeSubgroupStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetCardDivCardInfCommutativeSubgroup
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetCardDivCardInfCommutativeSubgroupStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.doubleCoset_card_div_card_inf_commutative_subgroup : ∀ {G : Type} [Group G] (T H U C : Subgroup G), (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) → U ≤ C → C ≤ T → U.relIndex C ≠ 0 → (Nat.card (DoubleCoset.Quotient ((H.subgroupOf T : Subgroup T) : Set T) ((U.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (H ⊓ U : Subgroup G) : ℂ) = (U.relIndex C : ℂ) * (Nat.card (DoubleCoset.Quotient ((H.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (H ⊓ C : Subgroup G) : ℂ) := by sorry
