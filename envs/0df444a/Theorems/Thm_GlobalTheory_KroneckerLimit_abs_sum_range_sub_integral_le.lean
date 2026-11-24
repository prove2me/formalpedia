-- Prove2me | Theorems.Thm_GlobalTheory_KroneckerLimit_abs_sum_range_sub_integral_le
-- name    : GlobalTheory.KroneckerLimit.abs_sum_range_sub_integral_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:50:48.310497+00:00
-- url     : https://prove2.me/theorems/1b01931d-be69-47d6-b256-fab8e817443a
-- title:
--   Kronecker Limit: abs sum range sub integral le
-- statement:
--   The Kronecker Limit construction uses the abs sum range sub integral le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/SummableAndAbsTsumSubIntegralLe.lean#L14-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/SummableAndAbsTsumSubIntegralLe.lean#L14-L74

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

theorem GlobalTheory.KroneckerLimit.abs_sum_range_sub_integral_le {f : ℝ → ℝ} (h0 : ∀ t, 0 ≤ f t) (hc : Continuous f)
    (hm : MonotoneOn f (Iic 0)) (ha : AntitoneOn f (Ici 0)) (x : ℝ) (k : ℕ) :
    |∑ i ∈ Finset.range k, f (x + i) - ∫ t in x..x + k, f t| ≤ f 0 := by sorry
