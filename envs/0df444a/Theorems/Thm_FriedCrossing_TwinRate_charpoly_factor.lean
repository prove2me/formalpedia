-- Prove2me | Theorems.Thm_FriedCrossing_TwinRate_charpoly_factor
-- name    : FriedCrossing.TwinRate.charpoly_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:45:24.728507+00:00
-- url     : https://prove2.me/theorems/5b77463e-b3e8-531b-9587-16ab0d5bd6c6
-- title:
--   Twin Rate: charpoly factor
-- statement:
--   The characteristic polynomial of the cluster factors through the two branches:
--   z² − (tr M) z + det M = (z − (s* + τ w₊))(z − (s* + τ w₋)).
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L105-L115
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L105-L115

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate

theorem FriedCrossing.TwinRate.charpoly_factor {sStar τ a b : ℝ} (h : 0 ≤ disc a b) (z : ℝ) :
    z ^ 2 - clusterTrace sStar τ a * z + clusterDet sStar τ a b =
      (z - (sStar + τ * wPlus a b)) * (z - (sStar + τ * wMinus a b)) := by sorry
