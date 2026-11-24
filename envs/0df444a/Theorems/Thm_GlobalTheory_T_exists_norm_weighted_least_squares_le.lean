-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_norm_weighted_least_squares_le
-- name    : GlobalTheory.T.exists_norm_weighted_least_squares_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:37:12.631805+00:00
-- url     : https://prove2.me/theorems/946d545c-69f0-4089-b4c5-bd36b436bac7
-- title:
--   T: exists norm weighted least squares le
-- statement:
--   The T construction uses the exists norm weighted least squares le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeightedLeastSquaresBoundStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeightedLeastSquaresBoundStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBoundStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_norm_weighted_least_squares_le : ∀ (M g : ℕ) (L : Matrix (Fin M) (Fin g) ℝ), L.rank = g → ∃ K : ℝ, ∀ (D : Fin M → ℝ) (b : Fin M → ℝ), (∀ k, 0 < D k) → ‖((L.transpose * Matrix.diagonal D * L)⁻¹ * L.transpose * Matrix.diagonal D).mulVec b‖ ≤ K * ‖b‖ := by sorry
