-- Prove2me | Theorems.Thm_FriedCrossing_Branch_wMinus_root
-- name    : FriedCrossing.Branch.wMinus_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:51:39.704571+00:00
-- url     : https://prove2.me/theorems/17f17f14-cbcc-51c3-8705-0052f038ead5
-- title:
--   Branch: w Minus root
-- statement:
--   The Branch construction uses the w Minus root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L734-L736
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L734-L736

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Branch
open TwinRate PureZeros

theorem FriedCrossing.Branch.wMinus_root {a b : ℝ} (hD : 0 ≤ disc a b) : wMinus a b ^ 2 - a * wMinus a b + b = 0 := by sorry
