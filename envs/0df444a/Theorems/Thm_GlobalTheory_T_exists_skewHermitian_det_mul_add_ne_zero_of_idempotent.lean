-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_skewHermitian_det_mul_add_ne_zero_of_idempotent
-- name    : GlobalTheory.T.exists_skewHermitian_det_mul_add_ne_zero_of_idempotent
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:38:07.725813+00:00
-- url     : https://prove2.me/theorems/5c775be9-a942-4c91-b5bc-327ad9d4470b
-- title:
--   T: exists skew Hermitian det mul add ne zero of idempotent
-- statement:
--   The T construction uses the exists skew Hermitian det mul add ne zero of idempotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SkewHermitianPerturbIdempotentDetNeZeroStatement.lean#L6-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SkewHermitianPerturbIdempotentDetNeZeroStatement.lean#L6-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SkewHermitianPerturbIdempotentDetNeZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SkewHermitianPerturbIdempotentDetNeZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_skewHermitian_det_mul_add_ne_zero_of_idempotent : ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (E D : Matrix (Fin n) (Fin n) k), E * E = E → (E.map σ)ᵀ = E → E * (D.map σ)ᵀ + D * E = 0 →
    (∀ a : Fin n → k, a ᵥ* E = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (E * V + D).det ≠ 0 := by sorry
