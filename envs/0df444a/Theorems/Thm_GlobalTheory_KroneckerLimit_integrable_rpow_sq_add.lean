-- Prove2me | Theorems.Thm_GlobalTheory_KroneckerLimit_integrable_rpow_sq_add
-- name    : GlobalTheory.KroneckerLimit.integrable_rpow_sq_add
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:51:05.169894+00:00
-- url     : https://prove2.me/theorems/b034d116-6320-437d-90f0-c651ffa67f4b
-- title:
--   Kronecker Limit: integrable rpow sq add
-- statement:
--   The Kronecker Limit construction uses the integrable rpow sq add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/SummableAndAbsTsumSubIntegralLe.lean#L187-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/SummableAndAbsTsumSubIntegralLe.lean#L187-L197

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Real
open GlobalTheory GlobalTheory.KroneckerLimit

theorem GlobalTheory.KroneckerLimit.integrable_rpow_sq_add {Y s : ℝ} (hY : 0 < Y) (hs : 1 ≤ s) :
    Integrable (fun t : ℝ => (t ^ 2 + Y ^ 2) ^ (-s)) := by sorry
