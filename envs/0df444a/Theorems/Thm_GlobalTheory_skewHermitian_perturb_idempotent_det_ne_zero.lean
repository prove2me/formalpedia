-- Prove2me | Theorems.Thm_GlobalTheory_skewHermitian_perturb_idempotent_det_ne_zero
-- name    : GlobalTheory.skewHermitian_perturb_idempotent_det_ne_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:20:43.152822+00:00
-- url     : https://prove2.me/theorems/281dee70-959f-42f8-93d7-5dbd565a9a59
-- title:
--   Global Theory: skew Hermitian perturb idempotent det ne zero
-- statement:
--   The Global Theory construction uses the skew Hermitian perturb idempotent det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SkewHermitianPerturbIdempotentDetNeZero.lean#L6-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SkewHermitianPerturbIdempotentDetNeZero.lean#L6-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SkewHermitianPerturbIdempotentDetNeZero
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

theorem GlobalTheory.skewHermitian_perturb_idempotent_det_ne_zero :
    ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (E D : Matrix (Fin n) (Fin n) k), E * E = E → (E.map σ)ᵀ = E → E * (D.map σ)ᵀ + D * E = 0 →
    (∀ a : Fin n → k, a ᵥ* E = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (E * V + D).det ≠ 0 := by sorry
