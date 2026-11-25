-- Prove2me | Theorems.Thm_GlobalTheory_T_invariantForm_normalizedHeisenbergIntertwiner
-- name    : GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:35:38.764059+00:00
-- url     : https://prove2.me/theorems/e66a04f0-f4e0-4c62-9f22-d6667ec496f1
-- title:
--   T: invariant Form normalized Heisenberg Intertwiner
-- statement:
--   The T construction uses the invariant Form normalized Heisenberg Intertwiner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvariantFormNormalizedHeisenbergIntertwinerStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvariantFormNormalizedHeisenbergIntertwinerStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvariantFormNormalizedHeisenbergIntertwiner
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergIntertwiningSumsCompEqIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedHeisenbergIntertwinerComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntertwinerHeisenbergCocycleOfFixedVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsWeilRepresentationHeisenberg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanHeisenbergTranslatesVacuumEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvariantFormNormalizedHeisenbergIntertwinerStatement
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

theorem GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → (∀ x y, ‖γ x y‖ = 1) → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ A : Submodule R X, SelfDual γ A → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ → ∀ (φ : X →ₗ[R] X), (∀ x y, γ (φ x) (φ y) = γ x y) → SelfDual γ (A.map φ) → idx A (A.map φ) ≠ 0 → ∀ T : M →ₗ[ℂ] M, (∀ x v, T (W x v) = W (φ x) (T v)) → (∀ e, Fixes W A e → T e = normOp lam W A (A.map φ) e) → ∀ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ x u v, B (W x u) (W x v) = B u v) → ∀ u v, B (T u) (T v) = B u v := by sorry
