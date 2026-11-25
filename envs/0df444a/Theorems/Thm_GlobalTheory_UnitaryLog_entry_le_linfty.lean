-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryLog_entry_le_linfty
-- name    : GlobalTheory.UnitaryLog.entry_le_linfty
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:42:01.237198+00:00
-- url     : https://prove2.me/theorems/be023660-77cc-5e22-8a31-35703094e359
-- title:
--   Unitary Log: entry le linfty
-- statement:
--   The Unitary Log construction uses the entry le linfty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsLogNearOneUnitaryGroupOfFormLinearBound.lean#L8-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsLogNearOneUnitaryGroupOfFormLinearBound.lean#L8-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsLogNearOneUnitaryGroupOfFormLinearBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open GlobalTheory GlobalTheory.UnitaryLog
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem GlobalTheory.UnitaryLog.entry_le_linfty {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖X i j‖ ≤ ‖X‖ := by sorry
