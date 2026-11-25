-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_hermitian_two_det_ne_zero
-- name    : GlobalTheory.T.exists_hermitian_two_det_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:12.014811+00:00
-- url     : https://prove2.me/theorems/ecca707e-9d39-563d-aa7b-f800e3489275
-- title:
--   T: exists hermitian two det ne zero
-- statement:
--   The T construction uses the exists hermitian two det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsHermitianDetNeZeroTwoStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsHermitianDetNeZeroTwoStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsHermitianDetNeZeroTwo
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsHermitianDetNeZeroTwoStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_hermitian_two_det_ne_zero : ∀ (E κ : Type) [Field E] [CharZero E] [Field κ] (σ : E →+* E) (φ : E →+* κ) (δ : E), δ ≠ 0 → σ δ = -δ → ∀ (n : ℕ) (c d y c' d' y' : Matrix (Fin n) (Fin n) κ), (c * y + d).det ≠ 0 → (c' * y' + d').det ≠ 0 → ∃ x : Matrix (Fin n) (Fin n) E, x.map σ = x.transpose ∧ (c * x.map φ + d).det ≠ 0 ∧ (c' * x.transpose.map φ + d').det ≠ 0 := by sorry
