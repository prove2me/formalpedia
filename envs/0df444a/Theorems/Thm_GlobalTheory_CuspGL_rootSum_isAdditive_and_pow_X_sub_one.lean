-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_rootSum_isAdditive_and_pow_X_sub_one
-- name    : GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:20:17.287857+00:00
-- url     : https://prove2.me/theorems/07e7a14c-a9c8-4f42-845b-7f41ccea68e9
-- title:
--   Cusp GL: root Sum is Additive and pow X sub one
-- statement:
--   The Cusp GL construction uses the root Sum is Additive and pow X sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RootPowerSumCharacterAdditiveAndXSubOnePow.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RootPowerSumCharacterAdditiveAndXSubOnePow.lean#L9-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharacterAdditiveAndXSubOnePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one :
    ∀ (F : Type) [Field F] (θ : AlgebraicClosure F →* ℂ) (k : ℕ),
      IsAdditive (rootSum θ k) ∧ ∀ j : ℕ, rootSum θ k ((X - C 1 : F[X]) ^ j) = j := by sorry
