-- Prove2me | Theorems.Thm_GlobalTheory_T_wittVector_existsUnique_sub_matrix_frobenius_eq
-- name    : GlobalTheory.T.wittVector_existsUnique_sub_matrix_frobenius_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:40:57.004655+00:00
-- url     : https://prove2.me/theorems/f7d8c93b-b1ab-41ed-b138-584144e4b31d
-- title:
--   T: witt Vector exists Unique sub matrix frobenius eq
-- statement:
--   The T construction uses the witt Vector exists Unique sub matrix frobenius eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WittVectorExistsUniqueSubMatrixFrobeniusEqStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WittVectorExistsUniqueSubMatrixFrobeniusEqStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WittVectorExistsUniqueSubMatrixFrobeniusEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WittVectorExistsUniqueSubMatrixFrobeniusEqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.wittVector_existsUnique_sub_matrix_frobenius_eq : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p] [PerfectRing R p] (ι : Type) [Fintype ι] (M : Matrix ι ι (WittVector p R)), (∀ c : ι → R, ∃! x : ι → R, x - (M.map WittVector.constantCoeff).mulVec (fun k => frobenius R p (x k)) = c) → ∀ c : ι → WittVector p R, ∃! v : ι → WittVector p R, v - M.mulVec (fun k => WittVector.frobenius (v k)) = c := by sorry
