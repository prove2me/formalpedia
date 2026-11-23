-- Prove2me | Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_WeightedSummable_mul
-- name    : GlobalTheory.CompleteHomogeneousBound.WeightedSummable.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:51.646803+00:00
-- url     : https://prove2.me/theorems/64e81345-f19d-475d-869b-d57d878eb2e3
-- title:
--   Weighted Summable: mul
-- statement:
--   The Weighted Summable construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormLeOfCompleteHomogeneousLe.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormLeOfCompleteHomogeneousLe.lean#L10-L19

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

theorem GlobalTheory.CompleteHomogeneousBound.WeightedSummable.mul {r : ℝ} {f g : ℂ⟦X⟧} (hf : WeightedSummable r f)
    (hg : WeightedSummable r g) : WeightedSummable r (f * g) := by sorry
