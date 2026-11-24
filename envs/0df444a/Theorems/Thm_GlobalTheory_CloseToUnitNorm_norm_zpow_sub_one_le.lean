-- Prove2me | Theorems.Thm_GlobalTheory_CloseToUnitNorm_norm_zpow_sub_one_le
-- name    : GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:40.029927+00:00
-- url     : https://prove2.me/theorems/a8f97e79-f641-455e-b1ab-bd0f91ca8019
-- title:
--   Close To Unit Norm: norm zpow sub one le
-- statement:
--   The Close To Unit Norm construction uses the norm zpow sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPowSubOneLe.lean#L28-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPowSubOneLe.lean#L28-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CloseToUnitNorm

theorem GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - (1 : C)‖ < (1 : ℝ)) (i : ℤ) : ‖u ^ i - (1 : C)‖ ≤ ‖u - (1 : C)‖ := by sorry
