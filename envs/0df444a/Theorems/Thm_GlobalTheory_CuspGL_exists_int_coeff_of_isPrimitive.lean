-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_exists_int_coeff_of_isPrimitive
-- name    : GlobalTheory.CuspGL.exists_int_coeff_of_isPrimitive
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:13:02.881456+00:00
-- url     : https://prove2.me/theorems/282eff6d-dfe1-4f10-a93d-ce4c2f1d0f50
-- title:
--   Cusp GL: exists int coeff of is Primitive
-- statement:
--   The Cusp GL construction uses the exists int coeff of is Primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsIntCoeffPrimitiveGLCharacter.lean#L17-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsIntCoeffPrimitiveGLCharacter.lean#L17-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveClassFunctionExpansionRootSumsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_GeneralLinearFunctionExtendZeroEndPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharpolyMemVirtualCharactersGLStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharacterInnerEqIntMulCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseOneProdIcoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharacterAdditiveAndXSubOnePowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIntCoeffPrimitiveGLCharacter
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

theorem GlobalTheory.CuspGL.exists_int_coeff_of_isPrimitive (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (d : ℕ) (χ : GL (Fin d) F → ℂ)
    (hd : 0 < d) (hχ : IsChar ℂ ℂ χ) (hp : IsPrimitive (extZero χ)) :
    ∃ a : ℕ → ℤ, (∀ k : ℕ, ipGL (extZero χ)
        (fun g : Module.End F (Fin d → F) => rootSum θ k (LinearMap.charpoly g)) = a k * glCard F d) ∧
      (d : ℂ) * χ 1 = (∑ k ∈ Finset.range (Nat.card F ^ d - 1), (a k : ℂ)) *
        ∏ i ∈ Finset.Ico 1 d, (1 - (Nat.card F : ℂ) ^ i) := by sorry
