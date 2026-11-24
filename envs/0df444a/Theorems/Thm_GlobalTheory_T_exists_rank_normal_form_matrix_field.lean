-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_rank_normal_form_matrix_field
-- name    : GlobalTheory.T.exists_rank_normal_form_matrix_field
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:38:38.060116+00:00
-- url     : https://prove2.me/theorems/ac2823ee-43d5-4a9b-a7df-50450b90b841
-- title:
--   T: exists rank normal form matrix field
-- statement:
--   The T construction uses the exists rank normal form matrix field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRankNormalFormMatrixFieldStatement.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRankNormalFormMatrixFieldStatement.lean#L6-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRankNormalFormMatrixField
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRankNormalFormMatrixFieldStatement
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

theorem GlobalTheory.T.exists_rank_normal_form_matrix_field : ∀ (k : Type) [Field k] (n : ℕ) (C : Matrix (Fin n) (Fin n) k),
    ∃ (U P : Matrix (Fin n) (Fin n) k) (e : Fin n → k), U.det ≠ 0 ∧ P.det ≠ 0 ∧ (∀ i, e i = 0 ∨ e i = 1) ∧
      U * C * P = Matrix.diagonal e := by sorry
