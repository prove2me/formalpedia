-- Prove2me | Theorems.Thm_GlobalTheory_T_matrix_entries_bounded_of_hermitian_log_trace_sq_le
-- name    : GlobalTheory.T.matrix_entries_bounded_of_hermitian_log_trace_sq_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:52:17.793411+00:00
-- url     : https://prove2.me/theorems/a82d22ac-72c5-4fa7-b1d1-01dc57ed2ca4
-- title:
--   T: matrix entries bounded of hermitian log trace sq le
-- statement:
--   The T construction uses the matrix entries bounded of hermitian log trace sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/MatrixEntriesBoundedOfHermitianLogTraceSqLeStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/MatrixEntriesBoundedOfHermitianLogTraceSqLeStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MatrixEntriesBoundedOfHermitianLogTraceSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MatrixEntriesBoundedOfHermitianLogTraceSqLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.matrix_entries_bounded_of_hermitian_log_trace_sq_le : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (E : ℝ), ∃ C : ℝ, ∀ x H : Matrix ι ι ℂ, IsLog H (xᴴ * x) → (Matrix.trace (H * H)).re ≤ E → ∀ i j, ‖x i j‖ ≤ C ∧ ‖H i j‖ ≤ C := by sorry
