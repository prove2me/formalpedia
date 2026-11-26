-- Prove2me | Theorems.Thm_FriedCrossing_ParamInt_contDiff_uncurry_partialX
-- name    : FriedCrossing.ParamInt.contDiff_uncurry_partialX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:52:40.824498+00:00
-- url     : https://prove2.me/theorems/f0c485c5-ae09-4165-acd3-3e2e31333f6d
-- title:
--   Param Int: cont Diff uncurry partial X
-- statement:
--   The Param Int construction uses the cont Diff uncurry partial X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L52-L60
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L52-L60

import Definitions.Def_B1s_resolvent_scale_9_11
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Definitions.Def_B1s_cluster_from_resolvent_9_11
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap MeasureTheory intervalIntegral Scale
open FriedCrossing.ParamInt

theorem FriedCrossing.ParamInt.contDiff_uncurry_partialX {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → ℝ → G) (n : ℕ)
    (hF : ContDiff ℝ (n + 1) (Function.uncurry F)) :
    ContDiff ℝ n (Function.uncurry (partialX F)) := by sorry
