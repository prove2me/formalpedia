-- Prove2me | Theorems.Thm_GlobalTheory_T_isCharacter_finsum_conj_subgroupFunctionExtendByZero
-- name    : GlobalTheory.T.isCharacter_finsum_conj_subgroupFunctionExtendByZero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:48:22.518353+00:00
-- url     : https://prove2.me/theorems/8d39c114-eb77-4a27-812d-961b4b78c4a2
-- title:
--   T: is Character finsum conj subgroup Function Extend By Zero
-- statement:
--   The T construction uses the is Character finsum conj subgroup Function Extend By Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterFinsumConjSubgroupFunctionExtendByZerStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterFinsumConjSubgroupFunctionExtendByZerStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterFinsumConjSubgroupFunctionExtendByZer
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterFinsumConjSubgroupFunctionExtendByZerStatement
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

theorem GlobalTheory.T.isCharacter_finsum_conj_subgroupFunctionExtendByZero : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), IsChar K L ψ → IsChar K L (fun g : G => ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out)) := by sorry
