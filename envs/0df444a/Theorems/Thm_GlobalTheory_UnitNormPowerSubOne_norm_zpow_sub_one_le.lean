-- Prove2me | Theorems.Thm_GlobalTheory_UnitNormPowerSubOne_norm_zpow_sub_one_le
-- name    : GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:52:21.159416+00:00
-- url     : https://prove2.me/theorems/d5146e84-b8e7-4695-96d2-8fc61b02b242
-- title:
--   Unit Norm Power Sub One: norm zpow sub one le
-- statement:
--   The Unit Norm Power Sub One construction uses the norm zpow sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormZpowSubOneLe.lean#L28-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormZpowSubOneLe.lean#L28-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitNormPowerSubOne

theorem GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - 1‖ < 1) (i : ℤ) : ‖u ^ i - 1‖ ≤ ‖u - 1‖ := by sorry
