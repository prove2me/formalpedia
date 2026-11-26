-- Prove2me | Theorems.Thm_FriedCrossing_TwinRate_branches_ne
-- name    : FriedCrossing.TwinRate.branches_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:45:19.165135+00:00
-- url     : https://prove2.me/theorems/00f0a120-0612-5e24-a8ef-72d20b24bc18
-- title:
--   Twin Rate: branches ne
-- statement:
--   For τ ≠ 0 and positive discriminant the two branches are distinct: the twin has
--   separated from the closed state.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L126-L132
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L126-L132

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate

theorem FriedCrossing.TwinRate.branches_ne {sStar τ a b : ℝ} (hτ : τ ≠ 0) (h : 0 < disc a b) :
    sStar + τ * wPlus a b ≠ sStar + τ * wMinus a b := by sorry
