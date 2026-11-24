-- Prove2me | Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_weightedSummable_one
-- name    : GlobalTheory.CompleteHomogeneousBound.weightedSummable_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:24:49.722012+00:00
-- url     : https://prove2.me/theorems/a8c1c40e-f0e0-4c14-9175-b061019a14eb
-- title:
--   Complete Homogeneous Bound: weighted Summable one
-- statement:
--   The Complete Homogeneous Bound construction uses the weighted Summable one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormLeOfCompleteHomogeneousLe.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormLeOfCompleteHomogeneousLe.lean#L21-L24

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

theorem GlobalTheory.CompleteHomogeneousBound.weightedSummable_one (r : ℝ) : WeightedSummable r 1 := by sorry
