-- Prove2me | Theorems.Thm_GlobalTheory_T_isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse
-- name    : GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:08.467803+00:00
-- url     : https://prove2.me/theorems/e24960b2-5632-4bcb-b2b8-a5065c102693
-- title:
--   T: is Primitive End Class Function invariant Subspace Mobius Inverse
-- statement:
--   The T construction uses the is Primitive End Class Function invariant Subspace Mobius Inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveEndClassFunctionInvariantSubspaceMobi
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
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

theorem GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → IsPrimitive (psi s V) := by sorry
