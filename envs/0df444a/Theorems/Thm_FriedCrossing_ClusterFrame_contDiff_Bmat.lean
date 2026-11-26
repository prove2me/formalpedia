-- Prove2me | Theorems.Thm_FriedCrossing_ClusterFrame_contDiff_Bmat
-- name    : FriedCrossing.ClusterFrame.contDiff_Bmat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:53:25.878733+00:00
-- url     : https://prove2.me/theorems/a28b04b7-bc09-4553-b302-2bc527a308f9
-- title:
--   Cluster Frame: cont Diff Bmat
-- statement:
--   The Cluster Frame construction uses the cont Diff Bmat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L168-L172
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L168-L172

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

theorem FriedCrossing.ClusterFrame.contDiff_Bmat (D : FrameData S k) (l j : Fin k) :
    ContDiff ℝ 3 fun p => Bmat F Jc D p l j := by sorry
