-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_eq_of_isPrimitive_of_eq_on_elliptic
-- name    : GlobalTheory.CuspGL.eq_of_isPrimitive_of_eq_on_elliptic
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:09:40.072985+00:00
-- url     : https://prove2.me/theorems/61f59625-cb3c-5f5d-b04c-94d2240a52b2
-- title:
--   Cusp GL: eq of is Primitive of eq on elliptic
-- statement:
--   The Cusp GL construction uses the eq of is Primitive of eq on elliptic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EqOfIsPrimitiveOfEqOnEllipticFiniteGL.lean#L213-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EqOfIsPrimitiveOfEqOnEllipticFiniteGL.lean#L213-L302

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

theorem GlobalTheory.CuspGL.eq_of_isPrimitive_of_eq_on_elliptic (F : Type) [Field F] [Finite F] (d : ℕ) (χ χ' : GL (Fin d) F → ℂ)
    (hd : 0 < d) (hi : _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ) (hi' : _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ') (hp : _root_.GlobalTheory.CuspGL.IsPrimitive (_root_.GlobalTheory.CuspGL.extZero χ))
    (hp' : _root_.GlobalTheory.CuspGL.IsPrimitive (_root_.GlobalTheory.CuspGL.extZero χ'))
    (he : ∀ x : GL (Fin d) F, Irreducible (Matrix.charpoly (x : Matrix (Fin d) (Fin d) F)) → χ x = χ' x) :
    χ = χ' := by sorry
