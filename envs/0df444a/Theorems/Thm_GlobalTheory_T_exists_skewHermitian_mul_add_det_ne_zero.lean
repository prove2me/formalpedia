-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_skewHermitian_mul_add_det_ne_zero
-- name    : GlobalTheory.T.exists_skewHermitian_mul_add_det_ne_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:38:20.67267+00:00
-- url     : https://prove2.me/theorems/e2b31a9b-e04f-403d-b6c6-68dfb000b9d1
-- title:
--   T: exists skew Hermitian mul add det ne zero
-- statement:
--   The T construction uses the exists skew Hermitian mul add det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSkewHermitianMulAddDetNeZeroOfPairStatement.lean#L6-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSkewHermitianMulAddDetNeZeroOfPairStatement.lean#L6-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSkewHermitianMulAddDetNeZeroOfPair
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSkewHermitianMulAddDetNeZeroOfPairStatement
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

theorem GlobalTheory.T.exists_skewHermitian_mul_add_det_ne_zero : ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (C D : Matrix (Fin n) (Fin n) k), C * (D.map σ)ᵀ + D * (C.map σ)ᵀ = 0 →
    (∀ a : Fin n → k, a ᵥ* C = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (C * V + D).det ≠ 0 := by sorry
