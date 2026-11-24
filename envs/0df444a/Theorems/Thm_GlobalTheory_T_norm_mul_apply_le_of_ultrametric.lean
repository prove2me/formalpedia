-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_mul_apply_le_of_ultrametric
-- name    : GlobalTheory.T.norm_mul_apply_le_of_ultrametric
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:37:12.041259+00:00
-- url     : https://prove2.me/theorems/64f5c2e8-b4c9-4d51-a316-b92a09919ea1
-- title:
--   T: norm mul apply le of ultrametric
-- statement:
--   The T construction uses the norm mul apply le of ultrametric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixMulEntryNormLeUltrametricStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixMulEntryNormLeUltrametricStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixMulEntryNormLeUltrametric
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixMulEntryNormLeUltrametricStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.norm_mul_apply_le_of_ultrametric : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n] (A B : Matrix n n E) (a b : ℝ), 0 ≤ a → 0 ≤ b → (∀ i j, ‖A i j‖ ≤ a) → (∀ i j, ‖B i j‖ ≤ b) → ∀ i j, ‖(A * B) i j‖ ≤ a * b := by sorry
