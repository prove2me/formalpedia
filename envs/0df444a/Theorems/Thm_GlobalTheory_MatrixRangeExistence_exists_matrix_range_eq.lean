-- Prove2me | Theorems.Thm_GlobalTheory_MatrixRangeExistence_exists_matrix_range_eq
-- name    : GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:48.994439+00:00
-- url     : https://prove2.me/theorems/32f93db9-a304-5429-b7d3-71eef002c72d
-- title:
--   Matrix Range Existence: exists matrix range eq
-- statement:
--   The Matrix Range Existence construction uses the exists matrix range eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixRangeEq.lean#L5-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixRangeEq.lean#L5-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatrixRangeEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MatrixRangeExistence

theorem GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (n : ℕ) (ϖ : O) (N : Submodule O (Fin n → O)) (hϖ : ϖ ≠ 0)
    (hN : ∀ y : Fin n → O, (fun a : Fin n => ϖ * y a) ∈ N) :
    ∃ A : Matrix (Fin n) (Fin n) O,
      (∀ x : Fin n → O, x ∈ N ↔ ∃ u : Fin n → O, Matrix.mulVec A u = x) ∧ Matrix.det A ≠ 0 := by sorry
