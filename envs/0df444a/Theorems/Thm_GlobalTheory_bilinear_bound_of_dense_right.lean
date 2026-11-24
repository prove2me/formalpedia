-- Prove2me | Theorems.Thm_GlobalTheory_bilinear_bound_of_dense_right
-- name    : GlobalTheory.bilinear_bound_of_dense_right
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:07:03.103675+00:00
-- url     : https://prove2.me/theorems/235c2d86-abfe-484f-9b8c-8c1cd29b0953
-- title:
--   Global Theory: bilinear bound of dense right
-- statement:
--   The Global Theory construction uses the bilinear bound of dense right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BilinearBoundOfDenseSecondSlot.lean#L8-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BilinearBoundOfDenseSecondSlot.lean#L8-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BilinearBoundOfDenseSecondSlot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped Uniformity
open GlobalTheory

theorem GlobalTheory.bilinear_bound_of_dense_right : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p →
    ∀ {X₁ X₂ : Type} [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂] [Module ℂ X₂]
    (j₁ : X₁ →ₗ[ℂ] E) (j₂ : X₂ →ₗ[ℂ] E), Function.Injective j₁ → IsClosed (Set.range j₁) →
    ∀ (D₂ : Submodule ℂ X₂), (∀ x, j₂ x ∈ closure (j₂ '' (D₂ : Set X₂))) →
    ∀ (F : X₁ →ₗ[ℂ] X₂ →ₗ[ℂ] E),
    (∀ w i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ b, p i (F w b) ≤ q (j₂ b)) →
    (∀ a ∈ D₂, ∀ i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w a) ≤ q (j₁ w)) →
    ∀ b i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w b) ≤ q (j₁ w) := by sorry
