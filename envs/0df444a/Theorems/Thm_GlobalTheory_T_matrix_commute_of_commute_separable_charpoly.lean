-- Prove2me | Theorems.Thm_GlobalTheory_T_matrix_commute_of_commute_separable_charpoly
-- name    : GlobalTheory.T.matrix_commute_of_commute_separable_charpoly
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:52:06.148065+00:00
-- url     : https://prove2.me/theorems/81f79568-d712-4ac9-b756-732e0bbf0556
-- title:
--   T: matrix commute of commute separable charpoly
-- statement:
--   The T construction uses the matrix commute of commute separable charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixCommuteOfCommuteSeparableCharpolyStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixCommuteOfCommuteSeparableCharpolyStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixCommuteOfCommuteSeparableCharpoly
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixCommuteOfCommuteSeparableCharpolyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.matrix_commute_of_commute_separable_charpoly : ∀ (E : Type) [Field E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E), A₀.charpoly.Separable → ∀ m n : Matrix (Fin r) (Fin r) E, m * A₀ = A₀ * m → n * A₀ = A₀ * n → m * n = n * m := by sorry
