-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_primary_conj_of_finrank_ker_eq
-- name    : GlobalTheory.CuspGL.primary_conj_of_finrank_ker_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:33:09.235796+00:00
-- url     : https://prove2.me/theorems/31689bbc-c41f-4226-8a64-ee5ee9bb2312
-- title:
--   Cusp GL: primary conj of finrank ker eq
-- statement:
--   The Cusp GL construction uses the primary conj of finrank ker eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ConjOfPrimaryFinrankKerPowEq.lean#L24-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ConjOfPrimaryFinrankKerPowEq.lean#L24-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimaryEndomorphismCyclicDecompositionFinrankKerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsPermOfSumMinEqPositiveFamilyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ConjOfPrimaryFinrankKerPowEq
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

theorem GlobalTheory.CuspGL.primary_conj_of_finrank_ker_eq : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g g' : Module.End F V) (f : F[X]) (m : ℕ), Irreducible f → aeval g (f ^ m) = 0 → aeval g' (f ^ m) = 0 → (∀ j : ℕ, Module.finrank F (LinearMap.ker (aeval g (f ^ j))) = Module.finrank F (LinearMap.ker (aeval g' (f ^ j)))) → ∃ e : V ≃ₗ[F] V, e.conj g = g' := by sorry
