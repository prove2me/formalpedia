-- Prove2me | Theorems.Thm_FriedCrossing_ClusterFrame_contDiff_riesz
-- name    : FriedCrossing.ClusterFrame.contDiff_riesz
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:43:45.692165+00:00
-- url     : https://prove2.me/theorems/a73a0f80-5cd5-5856-9725-0f82f96a802a
-- title:
--   Cluster Frame: cont Diff riesz
-- statement:
--   A C³ function of (p, λ) has C³ contour integrals in p.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L145-L157
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L145-L157

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

theorem FriedCrossing.ClusterFrame.contDiff_riesz (c : ℂ) (r : ℝ) (g : Param → ℂ) (hg : ContDiff ℝ 3 g) :
    ContDiff ℝ 3 (riesz c r g) := by sorry
