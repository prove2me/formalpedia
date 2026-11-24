-- Prove2me | Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_weightedSummable_prod
-- name    : GlobalTheory.CompleteHomogeneousBound.weightedSummable_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:39.550339+00:00
-- url     : https://prove2.me/theorems/fb53af57-5156-41c1-9c0b-74c7bfe28dca
-- title:
--   Complete Homogeneous Bound: weighted Summable prod
-- statement:
--   The Complete Homogeneous Bound construction uses the weighted Summable prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormLeOfCompleteHomogeneousLe.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormLeOfCompleteHomogeneousLe.lean#L32-L35

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

theorem GlobalTheory.CompleteHomogeneousBound.weightedSummable_prod {ι : Type*} (r : ℝ) (s : Finset ι) (f : ι → ℂ⟦X⟧)
    (h : ∀ i ∈ s, WeightedSummable r (f i)) : WeightedSummable r (∏ i ∈ s, f i) := by sorry
