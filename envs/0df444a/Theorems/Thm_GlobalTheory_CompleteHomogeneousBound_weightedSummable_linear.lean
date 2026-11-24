-- Prove2me | Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_weightedSummable_linear
-- name    : GlobalTheory.CompleteHomogeneousBound.weightedSummable_linear
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:24:47.377243+00:00
-- url     : https://prove2.me/theorems/8f21c015-2bde-463a-9c1f-b8c8a0064fd6
-- title:
--   Complete Homogeneous Bound: weighted Summable linear
-- statement:
--   The Complete Homogeneous Bound construction uses the weighted Summable linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormLeOfCompleteHomogeneousLe.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormLeOfCompleteHomogeneousLe.lean#L26-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
open GlobalTheory GlobalTheory.CompleteHomogeneousBound

theorem GlobalTheory.CompleteHomogeneousBound.weightedSummable_linear (r : ℝ) (b : ℂ) : WeightedSummable r (1 - C b * X) := by sorry
