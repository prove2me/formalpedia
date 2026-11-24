-- Prove2me | Theorems.Thm_GlobalTheory_matrix_one_add_pow_sub_entry_le
-- name    : GlobalTheory.matrix_one_add_pow_sub_entry_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:09:32.616513+00:00
-- url     : https://prove2.me/theorems/b3de1f0c-0333-4249-9f00-4d144ce91526
-- title:
--   Global Theory: matrix one add pow sub entry le
-- statement:
--   The Global Theory construction uses the matrix one add pow sub entry le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixOneAddPowSubEntryLe.lean#L16-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixOneAddPowSubEntryLe.lean#L16-L47

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

theorem GlobalTheory.matrix_one_add_pow_sub_entry_le :
    ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n]
      (Y : Matrix n n E) (t : ℝ), 0 ≤ t → t ≤ 1 → (∀ i j, ‖Y i j‖ ≤ t) →
      ∀ (m : ℕ) i j, ‖((1 + Y) ^ m - 1 - (m : E) • Y) i j‖ ≤ t ^ 2 := by sorry
