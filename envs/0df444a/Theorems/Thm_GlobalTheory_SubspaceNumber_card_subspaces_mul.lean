-- Prove2me | Theorems.Thm_GlobalTheory_SubspaceNumber_card_subspaces_mul
-- name    : GlobalTheory.SubspaceNumber.card_subspaces_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:33.732395+00:00
-- url     : https://prove2.me/theorems/cc741851-93e1-4653-8a86-497b4cb766c3
-- title:
--   Subspace Number: card subspaces mul
-- statement:
--   The Subspace Number construction uses the card subspaces mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CardSubspacesOfFinrankMulCardBases.lean#L32-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CardSubspacesOfFinrankMulCardBases.lean#L32-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesOfFinrankMulCardBases
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.SubspaceNumber

theorem GlobalTheory.SubspaceNumber.card_subspaces_mul :
    ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
      [FiniteDimensional F V] (a : ℕ), a ≤ Module.finrank F V →
      Nat.card {W : Submodule F V // Module.finrank F W = a} *
        ∏ i ∈ Finset.range a, (Nat.card F ^ a - Nat.card F ^ i) =
      ∏ i ∈ Finset.range a, (Nat.card F ^ Module.finrank F V - Nat.card F ^ i) := by sorry
