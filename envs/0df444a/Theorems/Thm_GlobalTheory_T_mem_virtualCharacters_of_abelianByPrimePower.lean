-- Prove2me | Theorems.Thm_GlobalTheory_T_mem_virtualCharacters_of_abelianByPrimePower
-- name    : GlobalTheory.T.mem_virtualCharacters_of_abelianByPrimePower
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:53:15.875719+00:00
-- url     : https://prove2.me/theorems/9c12426b-44fd-46e1-97d5-be1e34c71af4
-- title:
--   T: mem virtual Characters of abelian By Prime Power
-- statement:
--   The T construction uses the mem virtual Characters of abelian By Prime Power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/MemVirtualCharactersOfAbelianByPrimePowerStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/MemVirtualCharactersOfAbelianByPrimePowerStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MemVirtualCharactersOfAbelianByPrimePower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MemVirtualCharactersOfAbelianByPrimePowerStatement
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

theorem GlobalTheory.T.mem_virtualCharacters_of_abelianByPrimePower : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G], (∀ H : Subgroup G, AbByP H → ∀ ψ : H → L, IsChar L L ψ → IsChar K L ψ) → ∀ χ : G → L, IsChar L L χ → χ ∈ Virt K L G := by sorry
