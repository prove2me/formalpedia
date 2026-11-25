-- Prove2me | Theorems.Thm_GlobalTheory_exists_lt_norm_lt_one_of_densely
-- name    : GlobalTheory.exists_lt_norm_lt_one_of_densely
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:36.062136+00:00
-- url     : https://prove2.me/theorems/de13e93a-ae52-492f-9dd2-d3916366deaf
-- title:
--   Global Theory: exists lt norm lt one of densely
-- statement:
--   The Global Theory construction uses the exists lt norm lt one of densely property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ResidueNormValuationSubringEqZeroIff.lean#L356-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ResidueNormValuationSubringEqZeroIff.lean#L356-L359

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Filter Topology MvPowerSeries

theorem GlobalTheory.exists_lt_norm_lt_one_of_densely {C : Type*} [DenselyNormedField C] (r : ℝ) (hr : r < 1) :
    ∃ x : C, r < ‖x‖ ∧ ‖x‖ < 1 := by sorry
