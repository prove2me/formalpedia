-- Prove2me | Theorems.Thm_GlobalTheory_T_finsum_card_cyclic_vectors_invariant_subspaces
-- name    : GlobalTheory.T.finsum_card_cyclic_vectors_invariant_subspaces
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:39:28.053022+00:00
-- url     : https://prove2.me/theorems/a2be0b1c-902b-4a9e-9315-5f394837271a
-- title:
--   T: finsum card cyclic vectors invariant subspaces
-- statement:
--   The T construction uses the finsum card cyclic vectors invariant subspaces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinsumCardCyclicVectorsInvariantSubspacesStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinsumCardCyclicVectorsInvariantSubspacesStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumCardCyclicVectorsInvariantSubspaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumCardCyclicVectorsInvariantSubspacesStatement
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

theorem GlobalTheory.T.finsum_card_cyclic_vectors_invariant_subspaces : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V), ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, (Nat.card {v : W.1 // ∀ U : Submodule F (W.1), (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤} : ℂ) = (Nat.card F : ℂ) ^ Module.finrank F V := by sorry
