-- Prove2me | Theorems.Thm_GlobalTheory_KroneckerLimit_summable_and_abs_tsum_sub_integral_le
-- name    : GlobalTheory.KroneckerLimit.summable_and_abs_tsum_sub_integral_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:54:25.87899+00:00
-- url     : https://prove2.me/theorems/ed733fba-e044-4d39-986c-5700594ba7d8
-- title:
--   Kronecker Limit: summable and abs tsum sub integral le
-- statement:
--   The Kronecker Limit construction uses the summable and abs tsum sub integral le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/SummableAndAbsTsumSubIntegralLe.lean#L76-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/SummableAndAbsTsumSubIntegralLe.lean#L76-L139

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

theorem GlobalTheory.KroneckerLimit.summable_and_abs_tsum_sub_integral_le {f : ℝ → ℝ} (h0 : ∀ t, 0 ≤ f t) (hc : Continuous f)
    (hm : MonotoneOn f (Iic 0)) (ha : AntitoneOn f (Ici 0)) (hi : Integrable f) (a : ℝ) :
    Summable (fun n : ℤ => f (a + n)) ∧ |∑' n : ℤ, f (a + n) - ∫ t, f t| ≤ f 0 := by sorry
