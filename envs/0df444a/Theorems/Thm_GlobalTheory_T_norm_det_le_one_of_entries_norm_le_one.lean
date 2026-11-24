-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_det_le_one_of_entries_norm_le_one
-- name    : GlobalTheory.T.norm_det_le_one_of_entries_norm_le_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:54:57.498711+00:00
-- url     : https://prove2.me/theorems/89a81745-76fa-45c7-9270-62730cace31e
-- title:
--   T: norm det le one of entries norm le one
-- statement:
--   The T construction uses the norm det le one of entries norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormDetLeOneOfEntriesNormLeOneStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormDetLeOneOfEntriesNormLeOneStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormDetLeOneOfEntriesNormLeOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormDetLeOneOfEntriesNormLeOneStatement
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

theorem GlobalTheory.T.norm_det_le_one_of_entries_norm_le_one : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (x : Matrix (Fin n) (Fin n) E), (∀ i j, ‖x i j‖ ≤ 1) → ‖x.det‖ ≤ 1 := by sorry
