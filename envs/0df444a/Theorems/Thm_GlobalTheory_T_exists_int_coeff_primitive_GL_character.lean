-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_int_coeff_primitive_GL_character
-- name    : GlobalTheory.T.exists_int_coeff_primitive_GL_character
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:04:46.573883+00:00
-- url     : https://prove2.me/theorems/2cd2e424-dcce-4b2c-afc8-c1dc3491d4b8
-- title:
--   T: exists int coeff primitive GL character
-- statement:
--   The T construction uses the exists int coeff primitive GL character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsIntCoeffPrimitiveGLCharacterStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsIntCoeffPrimitiveGLCharacterStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIntCoeffPrimitiveGLCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIntCoeffPrimitiveGLCharacterStatement
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

theorem GlobalTheory.T.exists_int_coeff_primitive_GL_character : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (d : ℕ) (χ : GL (Fin d) F → ℂ), 0 < d → IsChar ℂ ℂ χ → IsPrimitive (extZero χ) → ∃ a : ℕ → ℤ, (∀ k : ℕ, ipGL (extZero χ) (fun g : Module.End F (Fin d → F) => rootSum θ k (LinearMap.charpoly g)) = a k * glCard F d) ∧ (d : ℂ) * χ 1 = (∑ k ∈ Finset.range (Nat.card F ^ d - 1), (a k : ℂ)) * ∏ i ∈ Finset.Ico 1 d, (1 - (Nat.card F : ℂ) ^ i) := by sorry
