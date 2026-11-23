-- Prove2me | Theorems.Thm_GlobalTheory_KroneckerLimit_summable_zero_row
-- name    : GlobalTheory.KroneckerLimit.summable_zero_row
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:58.175816+00:00
-- url     : https://prove2.me/theorems/7974f495-d276-4a93-a185-a2737a76456e
-- title:
--   Kronecker Limit: summable zero row
-- statement:
--   The Kronecker Limit construction uses the summable zero row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoRealEisensteinSubPole.lean#L188-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoRealEisensteinSubPole.lean#L188-L192

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
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

theorem GlobalTheory.KroneckerLimit.summable_zero_row {s : ℝ} (hs : 1 ≤ s) :
    Summable (fun n : ℤ => (((0 : ℝ) + n) ^ 2 + 0 ^ 2) ^ (-s)) := by sorry
