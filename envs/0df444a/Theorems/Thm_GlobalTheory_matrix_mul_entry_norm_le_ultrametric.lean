-- Prove2me | Theorems.Thm_GlobalTheory_matrix_mul_entry_norm_le_ultrametric
-- name    : GlobalTheory.matrix_mul_entry_norm_le_ultrametric
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:09:47.980821+00:00
-- url     : https://prove2.me/theorems/b5bdf118-e8b7-4870-85f5-fb50ca44d343
-- title:
--   Global Theory: matrix mul entry norm le ultrametric
-- statement:
--   The Global Theory construction uses the matrix mul entry norm le ultrametric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixMulEntryNormLeUltrametric.lean#L5-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixMulEntryNormLeUltrametric.lean#L5-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixMulEntryNormLeUltrametric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.matrix_mul_entry_norm_le_ultrametric :
    ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n]
      (A B : Matrix n n E) (a b : ℝ), 0 ≤ a → 0 ≤ b → (∀ i j, ‖A i j‖ ≤ a) → (∀ i j, ‖B i j‖ ≤ b) →
      ∀ i j, ‖(A * B) i j‖ ≤ a * b := by sorry
