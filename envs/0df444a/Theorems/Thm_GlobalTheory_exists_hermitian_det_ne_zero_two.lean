-- Prove2me | Theorems.Thm_GlobalTheory_exists_hermitian_det_ne_zero_two
-- name    : GlobalTheory.exists_hermitian_det_ne_zero_two
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:32:41.40513+00:00
-- url     : https://prove2.me/theorems/7bd7d760-d1e2-4f57-8a0a-b6aa7c226171
-- title:
--   Global Theory: exists hermitian det ne zero two
-- statement:
--   The Global Theory construction uses the exists hermitian det ne zero two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsHermitianDetNeZeroTwo.lean#L37-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsHermitianDetNeZeroTwo.lean#L37-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsHermitianDetNeZeroTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial Matrix

theorem GlobalTheory.exists_hermitian_det_ne_zero_two :
    ∀ (E κ : Type) [Field E] [CharZero E] [Field κ] (σ : E →+* E) (φ : E →+* κ) (δ : E), δ ≠ 0 → σ δ = -δ → ∀ (n : ℕ) (c d y c' d' y' : Matrix (Fin n) (Fin n) κ), (c * y + d).det ≠ 0 → (c' * y' + d').det ≠ 0 → ∃ x : Matrix (Fin n) (Fin n) E, x.map σ = x.transpose ∧ (c * x.map φ + d).det ≠ 0 ∧ (c' * x.transpose.map φ + d').det ≠ 0 := by sorry
