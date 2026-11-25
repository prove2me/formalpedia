-- Prove2me | Theorems.Thm_GlobalTheory_T_irreducibleCharacter_linear_or_induced_abelianByPrimePower
-- name    : GlobalTheory.T.irreducibleCharacter_linear_or_induced_abelianByPrimePower
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:47:43.97261+00:00
-- url     : https://prove2.me/theorems/5c40b80a-67c8-4295-8af6-b7c604aab54a
-- title:
--   T: irreducible Character linear or induced abelian By Prime Power
-- statement:
--   The T construction uses the irreducible Character linear or induced abelian By Prime Power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IrreducibleCharacterLinearOrInducedAbelianByPrimStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IrreducibleCharacterLinearOrInducedAbelianByPrimStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleCharacterLinearOrInducedAbelianByPrim
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleCharacterLinearOrInducedAbelianByPrimStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.irreducibleCharacter_linear_or_induced_abelianByPrimePower : ∀ (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (G : Type) [Group G] [Finite G] (χ : G → L), AbByP G → IsIrrChar L L χ → (∃ lam : G →* Lˣ, ∀ g, χ g = (lam g : L)) ∨ ∃ T : Subgroup G, T ≠ ⊤ ∧ ∃ ψ : T → L, IsChar L L ψ ∧ χ = ind T ψ := by sorry
