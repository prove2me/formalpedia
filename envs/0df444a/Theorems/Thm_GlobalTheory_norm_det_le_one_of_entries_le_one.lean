-- Prove2me | Theorems.Thm_GlobalTheory_norm_det_le_one_of_entries_le_one
-- name    : GlobalTheory.norm_det_le_one_of_entries_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:07.459799+00:00
-- url     : https://prove2.me/theorems/9bc3164f-5ba5-45f0-899c-85cc1dce96e6
-- title:
--   Global Theory: norm det le one of entries le one
-- statement:
--   The Global Theory construction uses the norm det le one of entries le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormDetLeOneOfEntriesNormLeOne.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormDetLeOneOfEntriesNormLeOne.lean#L7-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormDetLeOneOfEntriesNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
open GlobalTheory

theorem GlobalTheory.norm_det_le_one_of_entries_le_one :
    ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ)
      (x : Matrix (Fin n) (Fin n) E), (∀ i j, ‖x i j‖ ≤ 1) → ‖x.det‖ ≤ 1 := by sorry
