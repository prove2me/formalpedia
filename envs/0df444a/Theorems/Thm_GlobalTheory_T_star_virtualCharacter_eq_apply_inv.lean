-- Prove2me | Theorems.Thm_GlobalTheory_T_star_virtualCharacter_eq_apply_inv
-- name    : GlobalTheory.T.star_virtualCharacter_eq_apply_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:48.533394+00:00
-- url     : https://prove2.me/theorems/c5740254-df4c-4b9a-8ced-857319ca8bf0
-- title:
--   T: star virtual Character eq apply inv
-- statement:
--   The T construction uses the star virtual Character eq apply inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/StarVirtualCharacterEqApplyInvStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/StarVirtualCharacterEqApplyInvStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_StarVirtualCharacterEqApplyInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_StarVirtualCharacterEqApplyInvStatement
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

theorem GlobalTheory.T.star_virtualCharacter_eq_apply_inv : ∀ (G : Type) [Group G] [Finite G] (χ : G → ℂ), χ ∈ Virt ℂ ℂ G → ∀ g, star (χ g) = χ g⁻¹ := by sorry
