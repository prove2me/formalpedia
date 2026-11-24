-- Prove2me | Theorems.Thm_GlobalTheory_T_charpoly_block_and_invariant_under_stabilizerNilradical
-- name    : GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:52.03138+00:00
-- url     : https://prove2.me/theorems/3ee9f65b-45d5-4306-b8c6-f8efd9fa407b
-- title:
--   T: charpoly block and invariant under stabilizer Nilradical
-- statement:
--   The T construction uses the charpoly block and invariant under stabilizer Nilradical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CharpolyBlockAndInvariantUnderStabilizerNilradicStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CharpolyBlockAndInvariantUnderStabilizerNilradicStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
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

theorem GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A), LinearMap.charpoly g = LinearMap.charpoly (g.restrict hg) * LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx)) ∧ ∀ h ∈ nilRad A, LinearMap.charpoly (g + h) = LinearMap.charpoly g := by sorry
