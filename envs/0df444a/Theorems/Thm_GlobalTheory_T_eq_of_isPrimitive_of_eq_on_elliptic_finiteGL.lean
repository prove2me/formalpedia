-- Prove2me | Theorems.Thm_GlobalTheory_T_eq_of_isPrimitive_of_eq_on_elliptic_finiteGL
-- name    : GlobalTheory.T.eq_of_isPrimitive_of_eq_on_elliptic_finiteGL
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:10:47.829814+00:00
-- url     : https://prove2.me/theorems/7b98e336-4365-5a31-a1e5-b8d26e20537a
-- title:
--   T: eq of is Primitive of eq on elliptic finite GL
-- statement:
--   The T construction uses the eq of is Primitive of eq on elliptic finite GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EqOfIsPrimitiveOfEqOnEllipticFiniteGLStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EqOfIsPrimitiveOfEqOnEllipticFiniteGLStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqOfIsPrimitiveOfEqOnEllipticFiniteGL
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqOfIsPrimitiveOfEqOnEllipticFiniteGLStatement
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

theorem GlobalTheory.T.eq_of_isPrimitive_of_eq_on_elliptic_finiteGL : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (χ χ' : GL (Fin d) F → ℂ), 0 < d → IsIrrChar ℂ ℂ χ → IsIrrChar ℂ ℂ χ' → IsPrimitive (extZero χ) → IsPrimitive (extZero χ') → (∀ x : GL (Fin d) F, Irreducible (Matrix.charpoly (x : Matrix (Fin d) (Fin d) F)) → χ x = χ' x) → χ = χ' := by sorry
