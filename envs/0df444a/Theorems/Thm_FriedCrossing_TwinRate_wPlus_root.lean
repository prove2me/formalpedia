-- Prove2me | Theorems.Thm_FriedCrossing_TwinRate_wPlus_root
-- name    : FriedCrossing.TwinRate.wPlus_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:45:04.388131+00:00
-- url     : https://prove2.me/theorems/11b373eb-409e-47ba-a159-ee4b5d5c8d2e
-- title:
--   Twin Rate: w Plus root
-- statement:
--   The Twin Rate construction uses the w Plus root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L72-L79
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L72-L79

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate

theorem FriedCrossing.TwinRate.wPlus_root {a b : ℝ} (h : 0 ≤ disc a b) :
    wPlus a b ^ 2 - a * wPlus a b + b = 0 := by sorry
