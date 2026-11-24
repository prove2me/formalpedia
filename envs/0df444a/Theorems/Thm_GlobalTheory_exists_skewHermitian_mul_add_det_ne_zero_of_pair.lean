-- Prove2me | Theorems.Thm_GlobalTheory_exists_skewHermitian_mul_add_det_ne_zero_of_pair
-- name    : GlobalTheory.exists_skewHermitian_mul_add_det_ne_zero_of_pair
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:23.846047+00:00
-- url     : https://prove2.me/theorems/25bf06d6-bf06-4f59-a8e0-a31b6a774a3b
-- title:
--   Global Theory: exists skew Hermitian mul add det ne zero of pair
-- statement:
--   The Global Theory construction uses the exists skew Hermitian mul add det ne zero of pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSkewHermitianMulAddDetNeZeroOfPair.lean#L8-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSkewHermitianMulAddDetNeZeroOfPair.lean#L8-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRankNormalFormMatrixFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SkewHermitianPerturbIdempotentDetNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSkewHermitianMulAddDetNeZeroOfPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory

theorem GlobalTheory.exists_skewHermitian_mul_add_det_ne_zero_of_pair :
    ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (C D : Matrix (Fin n) (Fin n) k), C * (D.map σ)ᵀ + D * (C.map σ)ᵀ = 0 →
    (∀ a : Fin n → k, a ᵥ* C = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (C * V + D).det ≠ 0 := by sorry
