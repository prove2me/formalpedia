-- Prove2me | Theorems.Thm_GlobalTheory_T_sumOp_transversal_fixes_linear_and_of_le
-- name    : GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:59.84361+00:00
-- url     : https://prove2.me/theorems/f85eb5ac-5379-4171-85d7-4960972a00ab
-- title:
--   T: sum Op transversal fixes linear and of le
-- statement:
--   The T construction uses the sum Op transversal fixes linear and of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumOpTransversalStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumOpTransversalStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversalStatement
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

theorem GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ B → (∀ v, Fixes W A v → ∀ (ι : Type) [Fintype ι] (f : ι → X), (∀ i, f i ∈ B) → (∀ b ∈ B, ∃! i, b - f i ∈ A) → sumOp W A B v = ∑ i, W (f i) v ∧ idx A B = Fintype.card ι) ∧ (idx A B ≠ 0 → (∃ (n : ℕ) (f : Fin n → X), (∀ i, f i ∈ B) ∧ ∀ b ∈ B, ∃! i, b - f i ∈ A) ∧ (∀ v, Fixes W A v → Fixes W B (sumOp W A B v)) ∧ ∀ (c : ℂ) v, sumOp W A B (c • v) = c • sumOp W A B v) ∧ (B ≤ A → idx A B = 1 ∧ ∀ v, Fixes W A v → sumOp W A B v = v) := by sorry
