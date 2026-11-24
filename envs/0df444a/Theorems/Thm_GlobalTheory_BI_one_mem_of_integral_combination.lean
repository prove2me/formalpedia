-- Prove2me | Theorems.Thm_GlobalTheory_BI_one_mem_of_integral_combination
-- name    : GlobalTheory.BI.one_mem_of_integral_combination
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:00:42.641113+00:00
-- url     : https://prove2.me/theorems/50364568-5ba0-41fb-8218-2931ef5be714
-- title:
--   BI: one mem of integral combination
-- statement:
--   The BI construction uses the one mem of integral combination property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/OneMemVirtualCharactersOfIntegralCombination.lean#L9-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/OneMemVirtualCharactersOfIntegralCombination.lean#L9-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIntRelationOfIsIntegralRelationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharacterInnerEqIntMulCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OneMemVirtualCharactersOfIntegralCombination
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.BI

theorem GlobalTheory.BI.one_mem_of_integral_combination : ∀ (G : Type) [Group G] [Finite G] (S : AddSubgroup (G → ℂ)), S ≤ Virt ℂ ℂ G → ∀ (ι : Type) [Fintype ι] (r : ι → ℂ) (s : ι → G → ℂ), (∀ i, IsIntegral ℤ (r i)) → (∀ i, s i ∈ S) → (∀ g, ∑ i, r i * s i g = 1) → (1 : G → ℂ) ∈ S := by sorry
