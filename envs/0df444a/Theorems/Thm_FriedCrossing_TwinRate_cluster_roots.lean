-- Prove2me | Theorems.Thm_FriedCrossing_TwinRate_cluster_roots
-- name    : FriedCrossing.TwinRate.cluster_roots
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:39:09.847603+00:00
-- url     : https://prove2.me/theorems/93154a63-bdb1-5bdd-9160-7ddfefed43cd
-- title:
--   Twin Rate: cluster roots
-- statement:
--   The eigenvalues of the cluster are EXACTLY the two branches (no third resonance in the
--   disc): z is a root of the characteristic polynomial iff z = s* + τ w₊ or z = s* + τ w₋.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L119-L122
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L119-L122

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate

theorem FriedCrossing.TwinRate.cluster_roots {sStar τ a b : ℝ} (h : 0 ≤ disc a b) (z : ℝ) :
    z ^ 2 - clusterTrace sStar τ a * z + clusterDet sStar τ a b = 0 ↔
      z = sStar + τ * wPlus a b ∨ z = sStar + τ * wMinus a b := by sorry
