-- Prove2me | Theorems.Thm_FriedCrossing_ClusterFrame_contDiff_Mframe
-- name    : FriedCrossing.ClusterFrame.contDiff_Mframe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:53:40.441438+00:00
-- url     : https://prove2.me/theorems/baca2b02-45c3-59d2-a165-730403511ca3
-- title:
--   Cluster Frame: cont Diff Mframe
-- statement:
--   THE FRAME MATRIX IS C³ (given the frame is nondegenerate).
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L211-L215
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L211-L215

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

theorem FriedCrossing.ClusterFrame.contDiff_Mframe (D : FrameData S k) (hdet : ∀ p, (Amat F Jc D p).det ≠ 0) (l j : Fin k) :
    ContDiff ℝ 3 fun p => Mframe F Jc D p l j := by sorry
