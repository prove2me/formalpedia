-- Prove2me | Theorems.Thm_GlobalTheory_T_invertibleEndomorphismInnerProduct_primitive_mobiusInverse
-- name    : GlobalTheory.T.invertibleEndomorphismInnerProduct_primitive_mobiusInverse
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:46:55.04672+00:00
-- url     : https://prove2.me/theorems/9a105ad7-5954-40a5-b322-2b8b9978c31e
-- title:
--   T: invertible Endomorphism Inner Product primitive mobius Inverse
-- statement:
--   The T construction uses the invertible Endomorphism Inner Product primitive mobius Inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvertibleEndomorphismInnerProductPrimitiveMobiuStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvertibleEndomorphismInnerProductPrimitiveMobiuStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndomorphismInnerProductPrimitiveMobiu
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndomorphismInnerProductPrimitiveMobiuStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.invertibleEndomorphismInnerProduct_primitive_mobiusInverse : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ φ : Module.End F V → ℂ, IsPrimitive φ → ipGL φ (psi s V) = ipGL φ (fun g => s (LinearMap.charpoly g)) := by sorry
