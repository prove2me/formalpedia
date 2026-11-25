-- Prove2me | Theorems.Thm_GlobalTheory_irrChar_pi_eq_prod
-- name    : GlobalTheory.irrChar_pi_eq_prod
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:58:38.489198+00:00
-- url     : https://prove2.me/theorems/43cb36a9-c5ee-40ed-a00f-32ef93b2d370
-- title:
--   Global Theory: irr Char pi eq prod
-- statement:
--   The Global Theory construction uses the irr Char pi eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleCharacterOfProduct.lean#L131-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleCharacterOfProduct.lean#L131-L184

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingSelfIrreducibleAlgClos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_StarVirtualCharacterEqApplyInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingEqZeroOfDistinctIrredu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharacterIrreducibleExpansionNormSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleOfVirtualCharacterNormOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrrCharOneMulFinsumConjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleCharacterOfProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory
open IrrPi

theorem GlobalTheory.irrChar_pi_eq_prod : ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)] (χ : (∀ i, G i) → ℂ), IsIrrChar ℂ ℂ χ → ∃ ψ : ∀ i, G i → ℂ, (∀ i, IsIrrChar ℂ ℂ (ψ i)) ∧ ∀ x, χ x = ∏ i, ψ i (x i) := by sorry
