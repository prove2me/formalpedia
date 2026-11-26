-- Prove2me | Theorems.Thm_FriedCrossing_ClusterFrame_contDiff_Amat
-- name    : FriedCrossing.ClusterFrame.contDiff_Amat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:52:54.226079+00:00
-- url     : https://prove2.me/theorems/a447be9c-fccf-56e3-bc85-df824cc256e9
-- title:
--   Cluster Frame: cont Diff Amat
-- statement:
--   The Cluster Frame construction uses the cont Diff Amat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L163-L166
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L163-L166

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

theorem FriedCrossing.ClusterFrame.contDiff_Amat (D : FrameData S k) (l j : Fin k) :
    ContDiff ℝ 3 fun p => Amat F Jc D p l j := by sorry
