-- Prove2me | Theorems.Thm_FriedCrossing_HQuot_hasDerivAt_hq
-- name    : FriedCrossing.HQuot.hasDerivAt_hq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:49:31.141408+00:00
-- url     : https://prove2.me/theorems/577dce95-87f7-5d9b-b50b-f41f9104ec07
-- title:
--   HQuot: has Deriv At hq
-- statement:
--   The HQuot construction uses the has Deriv At hq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L302-L307
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L302-L307

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.HQuot

theorem FriedCrossing.HQuot.hasDerivAt_hq {f f' f'' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hc : ContinuousAt f'' 0) (τ : ℝ) :
    HasDerivAt (hq f f') (hq' f f' f'' τ) τ := by sorry
