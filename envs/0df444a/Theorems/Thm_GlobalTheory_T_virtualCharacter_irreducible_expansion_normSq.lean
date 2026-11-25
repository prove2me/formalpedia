-- Prove2me | Theorems.Thm_GlobalTheory_T_virtualCharacter_irreducible_expansion_normSq
-- name    : GlobalTheory.T.virtualCharacter_irreducible_expansion_normSq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:02:53.631365+00:00
-- url     : https://prove2.me/theorems/fb8b5d6a-5fd9-464d-80bb-fc8cdc96a610
-- title:
--   T: virtual Character irreducible expansion norm Sq
-- statement:
--   The T construction uses the virtual Character irreducible expansion norm Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/VirtualCharacterIrreducibleExpansionNormSqStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/VirtualCharacterIrreducibleExpansionNormSqStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharacterIrreducibleExpansionNormSq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharacterIrreducibleExpansionNormSqStatement
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

theorem GlobalTheory.T.virtualCharacter_irreducible_expansion_normSq : ∀ (G : Type) [Group G] [Finite G] (φ : G → ℂ), φ ∈ Virt ℂ ℂ G → ∃ c : (G → ℂ) →₀ ℤ, (∀ χ ∈ c.support, IsIrrChar ℂ ℂ χ) ∧ φ = c.sum (fun χ m => m • χ) ∧ ∑ᶠ g, φ g * star (φ g) = (c.sum fun _ m => (m : ℂ) ^ 2) * (Nat.card G : ℂ) := by sorry
