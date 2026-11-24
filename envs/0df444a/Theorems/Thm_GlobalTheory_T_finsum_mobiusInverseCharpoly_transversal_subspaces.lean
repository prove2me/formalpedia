-- Prove2me | Theorems.Thm_GlobalTheory_T_finsum_mobiusInverseCharpoly_transversal_subspaces
-- name    : GlobalTheory.T.finsum_mobiusInverseCharpoly_transversal_subspaces
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:40:08.033466+00:00
-- url     : https://prove2.me/theorems/405a02bd-73dd-4eb1-83a7-b52e88fbe806
-- title:
--   T: finsum mobius Inverse Charpoly transversal subspaces
-- statement:
--   The T construction uses the finsum mobius Inverse Charpoly transversal subspaces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinsumMobiusInverseCharpolyTransversalSubspacesStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinsumMobiusInverseCharpolyTransversalSubspacesStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyTransversalSubspaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyTransversalSubspacesStatement
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

theorem GlobalTheory.T.finsum_mobiusInverseCharpoly_transversal_subspaces : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ) (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A), ∑ᶠ x : {x : Module.End F V × Submodule F V // x.1 ∈ nilRad A ∧ x.2 ⊓ A = ⊥ ∧ ∀ v ∈ x.2, (g + x.1) v ∈ x.2}, psi s x.1.2 ((g + x.1.1).restrict x.2.2.2) = (Nat.card (nilRad A) : ℂ) * s (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))) := by sorry
