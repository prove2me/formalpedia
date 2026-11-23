-- Prove2me | Theorems.Thm_GlobalTheory_T_rootPowerSumCharacter_additive_and_X_sub_one_pow
-- name    : GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:15.945742+00:00
-- url     : https://prove2.me/theorems/105e4533-7fc2-4566-9409-55c69d065a1a
-- title:
--   T: root Power Sum Character additive and X sub one pow
-- statement:
--   The T construction uses the root Power Sum Character additive and X sub one pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RootPowerSumCharacterAdditiveAndXSubOnePowStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RootPowerSumCharacterAdditiveAndXSubOnePowStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharacterAdditiveAndXSubOnePow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharacterAdditiveAndXSubOnePowStatement
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

theorem GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow : ∀ (F : Type) [Field F] (θ : AlgebraicClosure F →* ℂ) (k : ℕ), IsAdditive (rootSum θ k) ∧ ∀ j : ℕ, rootSum θ k ((X - C 1 : F[X]) ^ j) = j := by sorry
