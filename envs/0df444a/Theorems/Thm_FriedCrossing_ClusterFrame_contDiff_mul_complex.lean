-- Prove2me | Theorems.Thm_FriedCrossing_ClusterFrame_contDiff_mul_complex
-- name    : FriedCrossing.ClusterFrame.contDiff_mul_complex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:53:40.393581+00:00
-- url     : https://prove2.me/theorems/cc30f95c-8724-4865-ade6-fa7efa6c14f9
-- title:
--   Cluster Frame: cont Diff mul complex
-- statement:
--   Entries of a product of C^m matrix families are C^m.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L203-L208
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L203-L208

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

theorem FriedCrossing.ClusterFrame.contDiff_mul_complex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : Type*} [Fintype n] {m : WithTop ℕ∞} {A B : E → Matrix n n ℂ}
    (hA : ∀ i j, ContDiff ℝ m fun x => A x i j) (hB : ∀ i j, ContDiff ℝ m fun x => B x i j)
    (i j : n) : ContDiff ℝ m fun x => (A x * B x) i j := by sorry
