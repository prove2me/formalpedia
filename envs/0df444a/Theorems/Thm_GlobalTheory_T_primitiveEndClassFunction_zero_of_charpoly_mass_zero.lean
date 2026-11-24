-- Prove2me | Theorems.Thm_GlobalTheory_T_primitiveEndClassFunction_zero_of_charpoly_mass_zero
-- name    : GlobalTheory.T.primitiveEndClassFunction_zero_of_charpoly_mass_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:56:45.516118+00:00
-- url     : https://prove2.me/theorems/fe62f07a-09de-4416-a12f-eef76e3888ca
-- title:
--   T: primitive End Class Function zero of charpoly mass zero
-- statement:
--   The T construction uses the primitive End Class Function zero of charpoly mass zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/PrimitiveEndClassFunctionZeroOfCharpolyMassZeroStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/PrimitiveEndClassFunctionZeroOfCharpolyMassZeroStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveEndClassFunctionZeroOfCharpolyMassZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveEndClassFunctionZeroOfCharpolyMassZeroStatement
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

theorem GlobalTheory.T.primitiveEndClassFunction_zero_of_charpoly_mass_zero : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → ∀ g : Module.End F V, mass φ (LinearMap.charpoly g) = 0 → φ g = 0 := by sorry
