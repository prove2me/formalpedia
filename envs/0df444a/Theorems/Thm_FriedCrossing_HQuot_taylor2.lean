-- Prove2me | Theorems.Thm_FriedCrossing_HQuot_taylor2
-- name    : FriedCrossing.HQuot.taylor2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:43:13.220148+00:00
-- url     : https://prove2.me/theorems/abd697ed-f718-4adb-9868-d79a73de4c05
-- title:
--   HQuot: taylor2
-- statement:
--   Second-order Taylor with Lagrange remainder, from two mean value theorems:
--   f(τ) − f(0) − τf'(0) = τ²f''(ξ)/2 with |ξ| < |τ|.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L230-L265
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L230-L265

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.HQuot

theorem FriedCrossing.HQuot.taylor2 {f f' f'' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) {τ : ℝ} (hτ : τ ≠ 0) :
    ∃ ξ, |ξ| < |τ| ∧ f τ - f 0 - τ * f' 0 = τ ^ 2 * f'' ξ / 2 := by sorry
