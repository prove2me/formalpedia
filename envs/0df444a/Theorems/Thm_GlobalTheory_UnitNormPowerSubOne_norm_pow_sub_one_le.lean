-- Prove2me | Theorems.Thm_GlobalTheory_UnitNormPowerSubOne_norm_pow_sub_one_le
-- name    : GlobalTheory.UnitNormPowerSubOne.norm_pow_sub_one_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:57:43.755364+00:00
-- url     : https://prove2.me/theorems/afdf2354-b39d-5054-801c-7c82c984c200
-- title:
--   Unit Norm Power Sub One: norm pow sub one le
-- statement:
--   The Unit Norm Power Sub One construction uses the norm pow sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormZpowSubOneLe.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormZpowSubOneLe.lean#L18-L26

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

theorem GlobalTheory.UnitNormPowerSubOne.norm_pow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - 1‖ < 1) (n : ℕ) : ‖u ^ n - 1‖ ≤ ‖u - 1‖ := by sorry
