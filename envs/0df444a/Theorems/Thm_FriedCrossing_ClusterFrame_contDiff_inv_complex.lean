-- Prove2me | Theorems.Thm_FriedCrossing_ClusterFrame_contDiff_inv_complex
-- name    : FriedCrossing.ClusterFrame.contDiff_inv_complex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:53:16.685578+00:00
-- url     : https://prove2.me/theorems/a23e8ba1-29b5-5a8f-b942-e1c71bdcb16d
-- title:
--   Cluster Frame: cont Diff inv complex
-- statement:
--   Entries of the inverse of a nonsingular C^m matrix family are C^m.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L192-L200
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L192-L200

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

theorem FriedCrossing.ClusterFrame.contDiff_inv_complex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : Type*} [Fintype n] [DecidableEq n] {m : WithTop ℕ∞} {A : E → Matrix n n ℂ}
    (h : ∀ i j, ContDiff ℝ m fun x => A x i j) (hdet : ∀ x, (A x).det ≠ 0) (i j : n) :
    ContDiff ℝ m fun x => (A x)⁻¹ i j := by sorry
