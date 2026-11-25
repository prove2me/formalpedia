-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_sum_coef_mul_eq_pair
-- name    : GlobalTheory.CuspGL.sum_coef_mul_eq_pair
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:30:15.797801+00:00
-- url     : https://prove2.me/theorems/5a564247-0995-5844-8393-cc22568e1ba3
-- title:
--   Cusp GL: sum coef mul eq pair
-- statement:
--   The Cusp GL construction uses the sum coef mul eq pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EqOfIsPrimitiveOfEqOnEllipticFiniteGL.lean#L33-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EqOfIsPrimitiveOfEqOnEllipticFiniteGL.lean#L33-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingSelfIrreducibleAlgClosStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_StarVirtualCharacterEqApplyInvStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIntCoeffPrimitiveGLCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGLStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyOfIrreduciStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_GeneralLinearFunctionExtendZeroEndPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingEqZeroOfDistinctIrreduStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndomorphismInnerProductPrimitiveMobiuStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OrthogonalIntVectorsNotAgreeOnRegular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsTeichmullerMapAlgebraicClosureFiniteFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FrobeniusTorusCharacterOrthogonalityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqOfIsPrimitiveOfEqOnEllipticFiniteGL
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

theorem GlobalTheory.CuspGL.sum_coef_mul_eq_pair (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (d : ℕ) (hd : 0 < d)
    (χ χ' : GL (Fin d) F → ℂ) (h : _root_.GlobalTheory.BI.IsChar ℂ ℂ χ) (h' : _root_.GlobalTheory.BI.IsChar ℂ ℂ χ')
    (hp : _root_.GlobalTheory.CuspGL.IsPrimitive (_root_.GlobalTheory.CuspGL.extZero χ)) (hp' : _root_.GlobalTheory.CuspGL.IsPrimitive (_root_.GlobalTheory.CuspGL.extZero χ')) (a b : ℕ → ℤ)
    (ha : ∀ k : ℕ, _root_.GlobalTheory.CuspGL.ipGL (_root_.GlobalTheory.CuspGL.extZero χ) (fun g : Module.End F (Fin d → F) => _root_.GlobalTheory.CuspGL.rootSum θ k (LinearMap.charpoly g))
      = a k * _root_.GlobalTheory.CuspGL.glCard F d)
    (hb : ∀ k : ℕ, _root_.GlobalTheory.CuspGL.ipGL (_root_.GlobalTheory.CuspGL.extZero χ') (fun g : Module.End F (Fin d → F) => _root_.GlobalTheory.CuspGL.rootSum θ k (LinearMap.charpoly g))
      = b k * _root_.GlobalTheory.CuspGL.glCard F d) :
    ((∑ k ∈ Finset.range (Nat.card F ^ d - 1), a k * b k : ℤ) : ℂ) = d * _root_.GlobalTheory.BI.pair χ χ' := by sorry
