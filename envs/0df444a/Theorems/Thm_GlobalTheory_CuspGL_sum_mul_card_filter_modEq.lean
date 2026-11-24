-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_sum_mul_card_filter_modEq
-- name    : GlobalTheory.CuspGL.sum_mul_card_filter_modEq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:33:52.869876+00:00
-- url     : https://prove2.me/theorems/051fcbaa-961d-481f-9ec9-e3463bf7b184
-- title:
--   Cusp GL: sum mul card filter mod Eq
-- statement:
--   The Cusp GL construction uses the sum mul card filter mod Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/PrimitiveClassFunctionExpansionRootSums.lean#L59-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/PrimitiveClassFunctionExpansionRootSums.lean#L59-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InnerProductRootPowerSumEqOfFrobeniusModEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndInnerProductRootPowerSumMobiusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndInnerProductRootPowerSumEqTorusSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveEndClassFunctionZeroOfCharpolyMassZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharacterAdditiveAndXSubOnePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfFinsumMulStarPowEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveClassFunctionExpansionRootSums
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

theorem GlobalTheory.CuspGL.sum_mul_card_filter_modEq (q n l : ℕ) (hq : 1 < q) (hn : 0 < n) (A : ℕ → ℂ)
    (hA : ∀ k i : ℕ, k * q ^ i ≡ l [MOD (q ^ n - 1)] → A k = A l) :
    ∑ k ∈ Finset.range (q ^ n - 1),
      A k * (((Finset.range n).filter (fun i => k * q ^ i ≡ l [MOD (q ^ n - 1)])).card : ℂ) = n * A l := by sorry
