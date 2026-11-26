-- Prove2me | Theorems.Thm_FriedCrossing_ClusterFrame_contDiff_melem
-- name    : FriedCrossing.ClusterFrame.contDiff_melem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:43:43.26229+00:00
-- url     : https://prove2.me/theorems/e517e0b3-865e-5db5-97f6-851eadd863e4
-- title:
--   Cluster Frame: cont Diff melem
-- statement:
--   Matrix elements of the resolvent with loss ≥ L 3 = 15 are C³ in (θ, τ, λ).
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L125-L135
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L125-L135

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

theorem FriedCrossing.ClusterFrame.contDiff_melem (a b : ℕ) (hab : b + 15 ≤ a) (φ : S.H a) (ℓ : S.H b →L[ℝ] ℝ) :
    ContDiff ℝ 3 (melem F Jc a b (by omega) φ ℓ) := by sorry
