-- Prove2me | Theorems.Thm_FriedCrossing_ParamInt_contDiff_parametric_intervalIntegral
-- name    : FriedCrossing.ParamInt.contDiff_parametric_intervalIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:52:48.238443+00:00
-- url     : https://prove2.me/theorems/c32e2b16-2b3c-4660-a1fa-109f246ac4a1
-- title:
--   Param Int: cont Diff parametric interval Integral
-- statement:
--   THE LEMMA. A jointly C^n integrand on a fixed compact interval integrates to a C^n function of
--   a finite-dimensional parameter. Induction on n; differentiation under the integral is dominated by
--   a constant from compactness of a closed ball times the interval.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L74-L113
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean#L74-L113

import Definitions.Def_B1s_resolvent_scale_9_11
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Definitions.Def_B1s_cluster_from_resolvent_9_11
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap MeasureTheory intervalIntegral Scale
open FriedCrossing.ParamInt

theorem FriedCrossing.ParamInt.contDiff_parametric_intervalIntegral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] (a b : ℝ) :
    ∀ (n : ℕ) (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      (F : E → ℝ → G), ContDiff ℝ n (Function.uncurry F) →
      ContDiff ℝ n fun x => ∫ t in a..b, F x t := by sorry
