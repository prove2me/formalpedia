-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_norm_choiceMatrix_le
-- name    : OAI.PiExponent.LiteralAnalytic.norm_choiceMatrix_le
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-10-11T21:56:08.032265+00:00
-- url     : https://prove2.me/theorems/f8e1da44-8abb-4180-b8fa-a555acbfdf08
-- title:
--   Original norm choiceMatrix le
-- statement:
--   For $H>0$, the original choice-matrix determinant norm is bounded by the exponential of its source multiplicity-square collision penalty and holomorphic-error budget. All binders, finite domains and hypotheses are precisely the accompanying original formal statement.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_CollisionCombinatorics_Multiplicity
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Log
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.LiteralAnalytic.norm_choiceMatrix_le {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    ‖(choiceMatrix d selection f).det‖ ≤ Real.exp
      (-(Real.log 2 / 4) * (∑ A : Transverse d H,
        (Collision.multiplicity Finset.univ (fun r => (f r).1) A : ℝ) ^ 2) +
        (actualRowCount d H : ℝ) * H *
          (d.holomorphicError + Collision.collisionRemainder (actualRowCount d H) H)) := by
  sorry
