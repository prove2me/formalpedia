-- Prove2me | Theorems.Thm_FriedCrossing_ClusterFrame_contDiff_det_complex
-- name    : FriedCrossing.ClusterFrame.contDiff_det_complex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:44:59.10546+00:00
-- url     : https://prove2.me/theorems/76ac546c-7bcb-49fc-b33f-019114766779
-- title:
--   Cluster Frame: cont Diff det complex
-- statement:
--   Determinants of ℂ-matrices with C^n entries (real smoothness).
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L175-L179
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L175-L179

import Definitions.Def_B1s_resolvent_scale_9_11
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Definitions.Def_B1s_cluster_from_resolvent_9_11
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap MeasureTheory intervalIntegral Scale
open FriedCrossing.ClusterFrame
open ParamInt
variable {S : BanachScale.{0}} (F : ResolventFamily S Param) (Jc : ComplexStructure S)
variable {k : ℕ}

theorem FriedCrossing.ClusterFrame.contDiff_det_complex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : Type*} [Fintype n] [DecidableEq n] {m : WithTop ℕ∞} {A : E → Matrix n n ℂ}
    (h : ∀ i j, ContDiff ℝ m fun x => A x i j) : ContDiff ℝ m fun x => (A x).det := by sorry
