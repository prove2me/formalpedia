-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_finsum_card_cyclic_eq
-- name    : GlobalTheory.CuspGL.finsum_card_cyclic_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:32:40.175637+00:00
-- url     : https://prove2.me/theorems/a9376d02-f867-4709-946b-b56f1762a792
-- title:
--   Cusp GL: finsum card cyclic eq
-- statement:
--   The Cusp GL construction uses the finsum card cyclic eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinsumCardCyclicVectorsInvariantSubspaces.lean#L7-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinsumCardCyclicVectorsInvariantSubspaces.lean#L7-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumCardCyclicVectorsInvariantSubspaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.finsum_card_cyclic_eq (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (g : Module.End F V) :
    ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W},
      (Nat.card {v : W.1 // ∀ U : Submodule F (W.1),
        (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤} : ℂ)
      = (Nat.card F : ℂ) ^ Module.finrank F V := by sorry
