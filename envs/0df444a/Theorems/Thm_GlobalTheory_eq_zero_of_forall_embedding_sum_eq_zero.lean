-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_forall_embedding_sum_eq_zero
-- name    : GlobalTheory.eq_zero_of_forall_embedding_sum_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:53:21.206981+00:00
-- url     : https://prove2.me/theorems/c23c516c-459b-4b91-9e85-7ddec71509a1
-- title:
--   Global Theory: eq zero of forall embedding sum eq zero
-- statement:
--   The Global Theory construction uses the eq zero of forall embedding sum eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallEmbeddingSumEqZero.lean#L5-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallEmbeddingSumEqZero.lean#L5-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallEmbeddingSumEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.eq_zero_of_forall_embedding_sum_eq_zero :
    ∀ (K K₁ : Type) [Field K] [CharZero K] [Field K₁] [Algebra K K₁] [FiniteDimensional K K₁] (σ₀ : K →+* ℂ) (n : ℕ) (e : Fin n → ℂ) (y : Fin n → K₁), (∀ c : Fin n → K, ∑ b, σ₀ (c b) * e b = 0 → c = 0) → (∀ σ₁ : K₁ →+* ℂ, σ₁.comp (algebraMap K K₁) = σ₀ → ∑ b, e b * σ₁ (y b) = 0) → y = 0 := by sorry
