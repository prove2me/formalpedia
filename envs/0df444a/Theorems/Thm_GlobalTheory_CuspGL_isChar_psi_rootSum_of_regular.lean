-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_isChar_psi_rootSum_of_regular
-- name    : GlobalTheory.CuspGL.isChar_psi_rootSum_of_regular
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:43:44.021345+00:00
-- url     : https://prove2.me/theorems/b2916f42-9cf2-4385-9a9f-3c1d7d3cdfad
-- title:
--   Cusp GL: is Char psi root Sum of regular
-- statement:
--   The Cusp GL construction uses the is Char psi root Sum of regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterCuspidalRootSumRegular.lean#L92-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterCuspidalRootSumRegular.lean#L92-L184

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_GeneralLinearFunctionExtendZeroEndPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndInnerProductRootPowerSumMobiusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharpolyMemVirtualCharactersGLStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleOfVirtualCharacterNormOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndomorphismInnerProductPrimitiveMobiuStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseOneProdIcoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ParabolicInductionTrivialPreservesVirtualCharact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharacterAdditiveAndXSubOnePowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterCuspidalRootSumRegular
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
open Polynomial

theorem GlobalTheory.CuspGL.isChar_psi_rootSum_of_regular (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (d k : ℕ) (hd : 0 < d)
    (hk : ∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1]) :
    _root_.GlobalTheory.BI.IsChar ℂ ℂ (fun x : GL (Fin d) F => (-1) ^ (d - 1) *
      _root_.GlobalTheory.CuspGL.psi (_root_.GlobalTheory.CuspGL.rootSum θ k) (Fin d → F) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))) ∧
    _root_.GlobalTheory.CuspGL.ipGL (_root_.GlobalTheory.CuspGL.psi (_root_.GlobalTheory.CuspGL.rootSum θ k) (Fin d → F)) (_root_.GlobalTheory.CuspGL.psi (_root_.GlobalTheory.CuspGL.rootSum θ k) (Fin d → F)) = _root_.GlobalTheory.CuspGL.glCard F d := by sorry
