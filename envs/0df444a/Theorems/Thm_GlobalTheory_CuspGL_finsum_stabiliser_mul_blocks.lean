-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_finsum_stabiliser_mul_blocks
-- name    : GlobalTheory.CuspGL.finsum_stabiliser_mul_blocks
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:32:43.596902+00:00
-- url     : https://prove2.me/theorems/e0844993-7c7b-4665-a75a-ad0407c9df1a
-- title:
--   Cusp GL: finsum stabiliser mul blocks
-- statement:
--   The Cusp GL construction uses the finsum stabiliser mul blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinsumSubspaceStabilizerMulBlockFunctions.lean#L7-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinsumSubspaceStabilizerMulBlockFunctions.lean#L7-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumSubspaceStabilizerMulBlockFunctions
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

theorem GlobalTheory.CuspGL.finsum_stabiliser_mul_blocks (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (W : Submodule F V) (Φ : Module.End F W → ℂ)
    (Φ' : Module.End F (V ⧸ W) → ℂ) :
    ∑ᶠ g : {g : Module.End F V // ∀ x ∈ W, g x ∈ W},
        Φ (g.1.restrict g.2) * Φ' (W.mapQ W g.1 (fun x hx => g.2 x hx)) =
      (Nat.card F : ℂ) ^ (Module.finrank F W * Module.finrank F (V ⧸ W)) *
        ((∑ᶠ a, Φ a) * ∑ᶠ b, Φ' b) := by sorry
