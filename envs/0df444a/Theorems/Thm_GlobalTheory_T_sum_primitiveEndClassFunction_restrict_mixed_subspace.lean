-- Prove2me | Theorems.Thm_GlobalTheory_T_sum_primitiveEndClassFunction_restrict_mixed_subspace
-- name    : GlobalTheory.T.sum_primitiveEndClassFunction_restrict_mixed_subspace
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:58:44.806403+00:00
-- url     : https://prove2.me/theorems/5ebaf846-2a7a-47c1-8d6a-d765de3ecd3a
-- title:
--   T: sum primitive End Class Function restrict mixed subspace
-- statement:
--   The T construction uses the sum primitive End Class Function restrict mixed subspace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SumPrimitiveEndClassFunctionRestrictMixedSubspacStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SumPrimitiveEndClassFunctionRestrictMixedSubspacStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumPrimitiveEndClassFunctionRestrictMixedSubspac
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumPrimitiveEndClassFunctionRestrictMixedSubspacStatement
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

theorem GlobalTheory.T.sum_primitiveEndClassFunction_restrict_mixed_subspace : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (A W : Submodule F V) (g : Module.End F V), (∀ x ∈ A, g x ∈ A) → W ⊓ A ≠ ⊥ → ¬ W ≤ A → ∀ φ : Module.End F W → ℂ, IsPrimitive φ → ∑ᶠ h : {h : Module.End F V // h ∈ nilRad A ∧ ∀ x ∈ W, (g + h) x ∈ W}, φ ((g + h.1).restrict h.2.2) = 0 := by sorry
