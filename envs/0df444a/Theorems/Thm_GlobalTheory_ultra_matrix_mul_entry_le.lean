-- Prove2me | Theorems.Thm_GlobalTheory_ultra_matrix_mul_entry_le
-- name    : GlobalTheory.ultra_matrix_mul_entry_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:24:32.387816+00:00
-- url     : https://prove2.me/theorems/ba11e040-8007-4156-b636-011b11b35cba
-- title:
--   Global Theory: ultra matrix mul entry le
-- statement:
--   The Global Theory construction uses the ultra matrix mul entry le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixOneAddPowSubEntryLe.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixOneAddPowSubEntryLe.lean#L7-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixOneAddPowSubEntryLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix

theorem GlobalTheory.ultra_matrix_mul_entry_le {E : Type} [NormedField E] [IsUltrametricDist E] {n : Type} [Fintype n]
    [DecidableEq n] (A B : Matrix n n E) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, ‖A i j‖ ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : n) : ‖(A * B) i j‖ ≤ a * b := by sorry
