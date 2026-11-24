-- Prove2me | Theorems.Thm_GlobalTheory_CloseToUnitNorm_norm_pow_sub_one_le
-- name    : GlobalTheory.CloseToUnitNorm.norm_pow_sub_one_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:13:56.303926+00:00
-- url     : https://prove2.me/theorems/125b3b1a-7b6e-48e8-bdd5-5d5a373dc662
-- title:
--   Close To Unit Norm: norm pow sub one le
-- statement:
--   The Close To Unit Norm construction uses the norm pow sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPowSubOneLe.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPowSubOneLe.lean#L17-L26

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

theorem GlobalTheory.CloseToUnitNorm.norm_pow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (hu : ‖u‖ = 1) (n : ℕ) : ‖u ^ n - 1‖ ≤ ‖u - 1‖ := by sorry
