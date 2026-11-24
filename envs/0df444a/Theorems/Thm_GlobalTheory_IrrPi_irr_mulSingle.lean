-- Prove2me | Theorems.Thm_GlobalTheory_IrrPi_irr_mulSingle
-- name    : GlobalTheory.IrrPi.irr_mulSingle
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:21:09.866903+00:00
-- url     : https://prove2.me/theorems/059ed9ef-a6ea-46f8-8fea-61c86b31d786
-- title:
--   Irr Pi: irr mul Single
-- statement:
--   The Irr Pi construction uses the irr mul Single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleCharacterOfProduct.lean#L35-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleCharacterOfProduct.lean#L35-L55

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
open GlobalTheory GlobalTheory.IrrPi

theorem GlobalTheory.IrrPi.irr_mulSingle {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)]
    [∀ i, Finite (G i)] {χ : (∀ i, G i) → ℂ} (h : IsIrrChar ℂ ℂ χ) (i : ι) (a : G i) (y : ∀ i, G i)
    (hy : y i = 1) : χ 1 * χ (Pi.mulSingle i a * y) = χ (Pi.mulSingle i a) * χ y := by sorry
