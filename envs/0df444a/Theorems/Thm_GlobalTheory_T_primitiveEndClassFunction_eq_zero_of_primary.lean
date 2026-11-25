-- Prove2me | Theorems.Thm_GlobalTheory_T_primitiveEndClassFunction_eq_zero_of_primary
-- name    : GlobalTheory.T.primitiveEndClassFunction_eq_zero_of_primary
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:55:28.110807+00:00
-- url     : https://prove2.me/theorems/2e4b40b4-6a30-4408-96b3-ead35de7e2fa
-- title:
--   T: primitive End Class Function eq zero of primary
-- statement:
--   The T construction uses the primitive End Class Function eq zero of primary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/PrimitiveEndClassFunctionEqZeroOfPrimaryStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/PrimitiveEndClassFunctionEqZeroOfPrimaryStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveEndClassFunctionEqZeroOfPrimary
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveEndClassFunctionEqZeroOfPrimaryStatement
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

theorem GlobalTheory.T.primitiveEndClassFunction_eq_zero_of_primary : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → ∀ (f : F[X]) (m : ℕ), Irreducible f → (∀ g : Module.End F V, LinearMap.charpoly g = f ^ m → aeval g f = 0 → φ g = 0) → ∀ g : Module.End F V, LinearMap.charpoly g = f ^ m → φ g = 0 := by sorry
