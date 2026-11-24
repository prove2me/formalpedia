-- Prove2me | Theorems.Thm_GlobalTheory_T_primary_endomorphism_cyclic_decomposition_finrank_ker
-- name    : GlobalTheory.T.primary_endomorphism_cyclic_decomposition_finrank_ker
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:54:51.922287+00:00
-- url     : https://prove2.me/theorems/74e8a230-4959-4f49-bb02-1dd3b4f5c12b
-- title:
--   T: primary endomorphism cyclic decomposition finrank ker
-- statement:
--   The T construction uses the primary endomorphism cyclic decomposition finrank ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/PrimaryEndomorphismCyclicDecompositionFinrankKerStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/PrimaryEndomorphismCyclicDecompositionFinrankKerStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimaryEndomorphismCyclicDecompositionFinrankKer
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimaryEndomorphismCyclicDecompositionFinrankKerStatement
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

theorem GlobalTheory.T.primary_endomorphism_cyclic_decomposition_finrank_ker : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V) (f : F[X]) (m : ℕ), Irreducible f → aeval g (f ^ m) = 0 → ∃ (d : ℕ) (e : Fin d → ℕ), (∀ i, 0 < e i) ∧ Nonempty (Module.AEval' g ≃ₗ[F[X]] ((i : Fin d) → F[X] ⧸ Ideal.span {f ^ e i})) ∧ ∀ j : ℕ, Module.finrank F (LinearMap.ker (aeval g (f ^ j))) = f.natDegree * ∑ i, min j (e i) := by sorry
