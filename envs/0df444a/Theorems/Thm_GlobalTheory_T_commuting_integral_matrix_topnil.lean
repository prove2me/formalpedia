-- Prove2me | Theorems.Thm_GlobalTheory_T_commuting_integral_matrix_topnil
-- name    : GlobalTheory.T.commuting_integral_matrix_topnil
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:30:28.278027+00:00
-- url     : https://prove2.me/theorems/045d3682-f0f3-47e9-be06-0216987013d7
-- title:
--   T: commuting integral matrix topnil
-- statement:
--   The T construction uses the commuting integral matrix topnil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommutingIntegralMatrixTopnilStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommutingIntegralMatrixTopnilStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixTopnil
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixTopnilStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.commuting_integral_matrix_topnil : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (N : Matrix (Fin n) (Fin n) E), (∀ i j, ‖N i j‖ ≤ 1) → (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧ u * N.charpoly + v * Polynomial.derivative N.charpoly = 1) → ∀ w : Matrix (Fin n) (Fin n) E, w * N = N * w → (∀ i j, ‖w i j‖ ≤ 1) → ∀ M : ℕ, (∀ i j, ‖(w ^ M) i j‖ < 1) → ∀ i j, ‖w i j‖ < 1 := by sorry
