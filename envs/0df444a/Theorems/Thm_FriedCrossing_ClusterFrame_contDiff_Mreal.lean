-- Prove2me | Theorems.Thm_FriedCrossing_ClusterFrame_contDiff_Mreal
-- name    : FriedCrossing.ClusterFrame.contDiff_Mreal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:53:49.647927+00:00
-- url     : https://prove2.me/theorems/227dde31-52ac-5c41-bf9c-87f2fe9bb3c1
-- title:
--   Cluster Frame: cont Diff Mreal
-- statement:
--   The Cluster Frame construction uses the cont Diff Mreal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L219-L225
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L219-L225

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

theorem FriedCrossing.ClusterFrame.contDiff_Mreal (D : FrameData S k) (hdet : ∀ p, (Amat F Jc D p).det ≠ 0) (i j : Fin k) :
    ContDiff ℝ 3 fun q : ℝ × ℝ => Mreal F Jc D q.1 q.2 i j := by sorry
