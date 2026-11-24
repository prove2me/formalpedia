-- Prove2me | Theorems.Thm_GlobalTheory_T_heisenbergSum_comp_of_adjacent_of_inf_eq
-- name    : GlobalTheory.T.heisenbergSum_comp_of_adjacent_of_inf_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:46:05.813814+00:00
-- url     : https://prove2.me/theorems/354d278c-a8c8-4496-aab8-41cd0d655282
-- title:
--   T: heisenberg Sum comp of adjacent of inf eq
-- statement:
--   The T construction uses the heisenberg Sum comp of adjacent of inf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HeisenbergSumCompOfAdjacentOfInfEqStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HeisenbergSumCompOfAdjacentOfInfEqStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergSumCompOfAdjacentOfInfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergSumCompOfAdjacentOfInfEqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.heisenbergSum_comp_of_adjacent_of_inf_eq : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → Adj A B → idx A C ≠ 0 → A ⊓ C = B ⊓ C → ∀ v, Fixes W A v → sumOp W B C (sumOp W A B v) = lam (idx A B) • sumOp W A C v := by sorry
