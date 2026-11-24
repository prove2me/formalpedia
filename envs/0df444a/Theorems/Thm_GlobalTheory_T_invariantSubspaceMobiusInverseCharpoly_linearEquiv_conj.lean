-- Prove2me | Theorems.Thm_GlobalTheory_T_invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj
-- name    : GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:54.1552+00:00
-- url     : https://prove2.me/theorems/af1d8021-350a-460b-be23-9daad9e00a85
-- title:
--   T: invariant Subspace Mobius Inverse Charpoly linear Equiv conj
-- statement:
--   The T construction uses the invariant Subspace Mobius Inverse Charpoly linear Equiv conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
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

theorem GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj : ∀ (F : Type) [Field F] (s : F[X] → ℂ) (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V), psi s V' (e.conj g) = psi s V g := by sorry
