-- Prove2me | Theorems.Thm_GlobalTheory_T_one_mem_virtualCharacters_of_integral_combination
-- name    : GlobalTheory.T.one_mem_virtualCharacters_of_integral_combination
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:55:07.904801+00:00
-- url     : https://prove2.me/theorems/d0969047-8bab-4f50-8c44-4135f4104592
-- title:
--   T: one mem virtual Characters of integral combination
-- statement:
--   The T construction uses the one mem virtual Characters of integral combination property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/OneMemVirtualCharactersOfIntegralCombinationStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/OneMemVirtualCharactersOfIntegralCombinationStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OneMemVirtualCharactersOfIntegralCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OneMemVirtualCharactersOfIntegralCombinationStatement
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

theorem GlobalTheory.T.one_mem_virtualCharacters_of_integral_combination : ∀ (G : Type) [Group G] [Finite G] (S : AddSubgroup (G → ℂ)), S ≤ Virt ℂ ℂ G → ∀ (ι : Type) [Fintype ι] (r : ι → ℂ) (s : ι → G → ℂ), (∀ i, IsIntegral ℤ (r i)) → (∀ i, s i ∈ S) → (∀ g, ∑ i, r i * s i g = 1) → (1 : G → ℂ) ∈ S := by sorry
