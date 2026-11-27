-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryLog_linfty_le_of_entries
-- name    : GlobalTheory.UnitaryLog.linfty_le_of_entries
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:42:12.09334+00:00
-- url     : https://prove2.me/theorems/af72014f-7d82-4784-ad16-4658c69069a6
-- title:
--   Unitary Log: linfty le of entries
-- statement:
--   The Unitary Log construction uses the linfty le of entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsLogNearOneUnitaryGroupOfFormLinearBound.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsLogNearOneUnitaryGroupOfFormLinearBound.lean#L15-L25

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

theorem GlobalTheory.UnitaryLog.linfty_le_of_entries {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ i j, ‖M i j‖ ≤ δ) : ‖M‖ ≤ n * δ := by sorry
