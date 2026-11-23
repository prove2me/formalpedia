-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_one_add_pow_sub_one_sub_smul_le_sq
-- name    : GlobalTheory.T.norm_one_add_pow_sub_one_sub_smul_le_sq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:43.699118+00:00
-- url     : https://prove2.me/theorems/1e397832-353f-4351-9a9d-7a426dfeeebd
-- title:
--   T: norm one add pow sub one sub smul le sq
-- statement:
--   The T construction uses the norm one add pow sub one sub smul le sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixOneAddPowSubEntryLeStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixOneAddPowSubEntryLeStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixOneAddPowSubEntryLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixOneAddPowSubEntryLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.norm_one_add_pow_sub_one_sub_smul_le_sq : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n] (Y : Matrix n n E) (t : ℝ), 0 ≤ t → t ≤ 1 → (∀ i j, ‖Y i j‖ ≤ t) → ∀ (m : ℕ) i j, ‖((1 + Y) ^ m - 1 - (m : E) • Y) i j‖ ≤ t ^ 2 := by sorry
