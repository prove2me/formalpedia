-- Prove2me | Theorems.Thm_GlobalTheory_T_virtualCharacter_inner_eq_int_mul_card
-- name    : GlobalTheory.T.virtualCharacter_inner_eq_int_mul_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:02.586083+00:00
-- url     : https://prove2.me/theorems/993dec2b-6d01-42a2-b15d-1f4804658657
-- title:
--   T: virtual Character inner eq int mul card
-- statement:
--   The T construction uses the virtual Character inner eq int mul card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/VirtualCharacterInnerEqIntMulCardStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/VirtualCharacterInnerEqIntMulCardStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharacterInnerEqIntMulCard
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharacterInnerEqIntMulCardStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.virtualCharacter_inner_eq_int_mul_card : ∀ (G : Type) [Group G] [Finite G] (a b : G → ℂ), a ∈ Virt ℂ ℂ G → b ∈ Virt ℂ ℂ G → ∃ m : ℤ, ∑ᶠ g, a g * star (b g) = m * (Nat.card G : ℂ) := by sorry
