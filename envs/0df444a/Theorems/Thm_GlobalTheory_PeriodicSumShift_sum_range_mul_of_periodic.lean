-- Prove2me | Theorems.Thm_GlobalTheory_PeriodicSumShift_sum_range_mul_of_periodic
-- name    : GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:57.907266+00:00
-- url     : https://prove2.me/theorems/5363ce55-b46c-431e-b89e-7c972b5b099c
-- title:
--   Periodic Sum Shift: sum range mul of periodic
-- statement:
--   The Periodic Sum Shift construction uses the sum range mul of periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumRangeMulOfPeriodic.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumRangeMulOfPeriodic.lean#L12-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumRangeMulOfPeriodic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PeriodicSumShift

theorem GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic : ∀ {K : Type} [inst : Field K] (g : ℕ → K) (N : ℕ),
    (∀ (i : ℕ), g (N + i) = g i) → ∀ (k : ℕ),
      ∑ i ∈ Finset.range (N * k), g i = (↑k : K) * ∑ i ∈ Finset.range N, g i := by sorry
