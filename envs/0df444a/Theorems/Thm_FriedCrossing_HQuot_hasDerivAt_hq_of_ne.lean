-- Prove2me | Theorems.Thm_FriedCrossing_HQuot_hasDerivAt_hq_of_ne
-- name    : FriedCrossing.HQuot.hasDerivAt_hq_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:49:12.111289+00:00
-- url     : https://prove2.me/theorems/e4b0a858-d05c-4af3-b717-1ff5b753ddc3
-- title:
--   HQuot: has Deriv At hq of ne
-- statement:
--   The HQuot construction uses the has Deriv At hq of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L267-L275
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L267-L275

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.HQuot

theorem FriedCrossing.HQuot.hasDerivAt_hq_of_ne {f f' f'' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) {τ : ℝ}
    (hτ : τ ≠ 0) : HasDerivAt (hq f f') (hq' f f' f'' τ) τ := by sorry
