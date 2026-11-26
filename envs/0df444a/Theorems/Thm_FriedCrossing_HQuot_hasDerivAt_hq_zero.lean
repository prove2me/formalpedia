-- Prove2me | Theorems.Thm_FriedCrossing_HQuot_hasDerivAt_hq_zero
-- name    : FriedCrossing.HQuot.hasDerivAt_hq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:49:13.726258+00:00
-- url     : https://prove2.me/theorems/7ab6b53c-8d29-56e6-97f5-eaee148cc572
-- title:
--   HQuot: has Deriv At hq zero
-- statement:
--   The HQuot construction uses the has Deriv At hq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L277-L300
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L277-L300

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.HQuot

theorem FriedCrossing.HQuot.hasDerivAt_hq_zero {f f' f'' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hc : ContinuousAt f'' 0) :
    HasDerivAt (hq f f') (hq' f f' f'' 0) 0 := by sorry
