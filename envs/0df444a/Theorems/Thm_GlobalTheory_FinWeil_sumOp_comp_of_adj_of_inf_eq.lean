-- Prove2me | Theorems.Thm_GlobalTheory_FinWeil_sumOp_comp_of_adj_of_inf_eq
-- name    : GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:29:49.26388+00:00
-- url     : https://prove2.me/theorems/e33d4e2e-cd8e-436c-b851-1143e9a21970
-- title:
--   Fin Weil: sum Op comp of adj of inf eq
-- statement:
--   The Fin Weil construction uses the sum Op comp of adj of inf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HeisenbergSumCompOfAdjacentOfInfEq.lean#L22-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HeisenbergSumCompOfAdjacentOfInfEq.lean#L22-L192

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PerfectPairingQuotients
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_AdjacentSelfDualLatticesIndexSimple
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergSumCompOfAdjacentOfInfEq
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
open GlobalTheory GlobalTheory.FinWeil
open Classical
open scoped BigOperators

theorem GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, _root_.GlobalTheory.FinWeil.GoodNorm σ lam → ∀ (A B C : Submodule R X), _root_.GlobalTheory.FinWeil.SelfDual γ A → _root_.GlobalTheory.FinWeil.SelfDual γ B → _root_.GlobalTheory.FinWeil.SelfDual γ C → _root_.GlobalTheory.FinWeil.Adj A B → _root_.GlobalTheory.FinWeil.idx A C ≠ 0 → A ⊓ C = B ⊓ C → ∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v → _root_.GlobalTheory.FinWeil.sumOp W B C (_root_.GlobalTheory.FinWeil.sumOp W A B v) = lam (_root_.GlobalTheory.FinWeil.idx A B) • _root_.GlobalTheory.FinWeil.sumOp W A C v := by sorry
