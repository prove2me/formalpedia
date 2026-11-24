-- Prove2me | Theorems.Thm_GlobalTheory_T_ultrametric_matrix_inv_near_one
-- name    : GlobalTheory.T.ultrametric_matrix_inv_near_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:01:13.376075+00:00
-- url     : https://prove2.me/theorems/84242823-b12a-47d8-854d-a6269cb279ae
-- title:
--   T: ultrametric matrix inv near one
-- statement:
--   The T construction uses the ultrametric matrix inv near one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UltrametricMatrixInvNearOneStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UltrametricMatrixInvNearOneStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricMatrixInvNearOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricMatrixInvNearOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.ultrametric_matrix_inv_near_one : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n] (X Z : Matrix n n E) (t : ℝ), 0 ≤ t → t < 1 → Z * X = 1 → (∀ i j, ‖(X - 1) i j‖ ≤ t) → ∀ i j, ‖(Z - 1) i j‖ ≤ t := by sorry
