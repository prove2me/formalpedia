-- Prove2me | Theorems.Thm_GlobalTheory_T_mem_virtualCharacters_iff_sub_characters
-- name    : GlobalTheory.T.mem_virtualCharacters_iff_sub_characters
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:52:30.571065+00:00
-- url     : https://prove2.me/theorems/e16e3a80-8cd5-4aed-a2ba-e50230817580
-- title:
--   T: mem virtual Characters iff sub characters
-- statement:
--   The T construction uses the mem virtual Characters iff sub characters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/MemVirtualCharactersIffSubCharactersStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/MemVirtualCharactersIffSubCharactersStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MemVirtualCharactersIffSubCharacters
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MemVirtualCharactersIffSubCharactersStatement
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

theorem GlobalTheory.T.mem_virtualCharacters_iff_sub_characters : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (f : G → L), f ∈ Virt K L G ↔ ∃ a b : G → L, IsChar K L a ∧ IsChar K L b ∧ f = a - b := by sorry
