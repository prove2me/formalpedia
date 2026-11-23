-- Prove2me | Theorems.Thm_GlobalTheory_FinWeil_sumOp_transversal
-- name    : GlobalTheory.FinWeil.sumOp_transversal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:49:41.794715+00:00
-- url     : https://prove2.me/theorems/26280cd7-0fd5-49dc-9c88-e8416236532e
-- title:
--   Fin Weil: sum Op transversal
-- statement:
--   The Fin Weil construction uses the sum Op transversal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumOpTransversal.lean#L148-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumOpTransversal.lean#L148-L176

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
open Classical
open scoped BigOperators

theorem GlobalTheory.FinWeil.sumOp_transversal : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M},
    _root_.GlobalTheory.FinWeil.IsHeis σ w γ W → ∀ (A B : Submodule R X),
    _root_.GlobalTheory.FinWeil.SelfDual γ B → (∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v → ∀ (ι : Type) [Fintype ι]
      (f : ι → X), (∀ i, f i ∈ B) → (∀ b ∈ B, ∃! i, b - f i ∈ A) →
      _root_.GlobalTheory.FinWeil.sumOp W A B v = ∑ i, W (f i) v ∧
        _root_.GlobalTheory.FinWeil.idx A B = Fintype.card ι) ∧
    (_root_.GlobalTheory.FinWeil.idx A B ≠ 0 → (∃ (n : ℕ) (f : Fin n → X), (∀ i, f i ∈ B) ∧
      ∀ b ∈ B, ∃! i, b - f i ∈ A) ∧
      (∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v →
        _root_.GlobalTheory.FinWeil.Fixes W B (_root_.GlobalTheory.FinWeil.sumOp W A B v)) ∧
      ∀ (c : ℂ) v, _root_.GlobalTheory.FinWeil.sumOp W A B (c • v) = c • _root_.GlobalTheory.FinWeil.sumOp W A B v) ∧
    (B ≤ A → _root_.GlobalTheory.FinWeil.idx A B = 1 ∧
      ∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v → _root_.GlobalTheory.FinWeil.sumOp W A B v = v) := by sorry
