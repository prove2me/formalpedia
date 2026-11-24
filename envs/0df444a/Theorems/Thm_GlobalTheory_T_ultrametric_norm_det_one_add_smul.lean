-- Prove2me | Theorems.Thm_GlobalTheory_T_ultrametric_norm_det_one_add_smul
-- name    : GlobalTheory.T.ultrametric_norm_det_one_add_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:50.621161+00:00
-- url     : https://prove2.me/theorems/cb64d753-48aa-49d8-b396-6e139ec399e3
-- title:
--   T: ultrametric norm det one add smul
-- statement:
--   The T construction uses the ultrametric norm det one add smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UltrametricNormDetOneAddSmulStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UltrametricNormDetOneAddSmulStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormDetOneAddSmul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormDetOneAddSmulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.ultrametric_norm_det_one_add_smul : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (x : Matrix (Fin n) (Fin n) E) (ϖ : E), ‖ϖ‖ < 1 → (∀ i j, ‖x i j‖ ≤ 1) → ‖(1 + ϖ • x).det‖ = 1 := by sorry
