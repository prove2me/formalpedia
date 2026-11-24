-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_isUnit_det_krylovMatrix_of_separable
-- name    : GlobalTheory.T.exists_isUnit_det_krylovMatrix_of_separable
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:37:02.263679+00:00
-- url     : https://prove2.me/theorems/25957c11-7f53-44db-b91b-1c41e9f44962
-- title:
--   T: exists is Unit det krylov Matrix of separable
-- statement:
--   The T construction uses the exists is Unit det krylov Matrix of separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsUnitDetKrylovMatrixOfSeparableStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsUnitDetKrylovMatrixOfSeparableStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsUnitDetKrylovMatrixOfSeparable
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrylovApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsUnitDetKrylovMatrixOfSeparableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_isUnit_det_krylovMatrix_of_separable : ∀ {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F), y.charpoly.Separable → ∃ e : Fin r → F, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det := by sorry
