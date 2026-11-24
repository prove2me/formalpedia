-- Prove2me | Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_weightedSummable_geom_iff
-- name    : GlobalTheory.CompleteHomogeneousBound.weightedSummable_geom_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:37.369873+00:00
-- url     : https://prove2.me/theorems/6da8d502-bb3d-4ee0-b0a8-a93d9033f264
-- title:
--   Complete Homogeneous Bound: weighted Summable geom iff
-- statement:
--   The Complete Homogeneous Bound construction uses the weighted Summable geom iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormLeOfCompleteHomogeneousLe.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormLeOfCompleteHomogeneousLe.lean#L37-L41

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

theorem GlobalTheory.CompleteHomogeneousBound.weightedSummable_geom_iff (r : ℝ) (b : ℂ) :
    WeightedSummable r (mk fun m => b ^ m) ↔ ‖b * r‖ < 1 := by sorry
