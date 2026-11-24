-- Prove2me | Theorems.Thm_GlobalTheory_T_finsum_subspaceStabilizer_mul_block_functions
-- name    : GlobalTheory.T.finsum_subspaceStabilizer_mul_block_functions
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:39:54.857155+00:00
-- url     : https://prove2.me/theorems/1d11a170-564d-4c15-9314-8dadf47fb9f4
-- title:
--   T: finsum subspace Stabilizer mul block functions
-- statement:
--   The T construction uses the finsum subspace Stabilizer mul block functions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinsumSubspaceStabilizerMulBlockFunctionsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinsumSubspaceStabilizerMulBlockFunctionsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumSubspaceStabilizerMulBlockFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumSubspaceStabilizerMulBlockFunctionsStatement
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

theorem GlobalTheory.T.finsum_subspaceStabilizer_mul_block_functions : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (W : Submodule F V) (Φ : Module.End F W → ℂ) (Φ' : Module.End F (V ⧸ W) → ℂ), ∑ᶠ g : {g : Module.End F V // ∀ x ∈ W, g x ∈ W}, Φ (g.1.restrict g.2) * Φ' (W.mapQ W g.1 (fun x hx => g.2 x hx)) = (Nat.card F : ℂ) ^ (Module.finrank F W * Module.finrank F (V ⧸ W)) * ((∑ᶠ a, Φ a) * ∑ᶠ b, Φ' b) := by sorry
