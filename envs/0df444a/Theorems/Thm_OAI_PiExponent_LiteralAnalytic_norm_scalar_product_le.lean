-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_norm_scalar_product_le
-- name    : OAI.PiExponent.LiteralAnalytic.norm_scalar_product_le
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-11T21:55:41.466988+00:00
-- url     : https://prove2.me/theorems/bb24bb55-f393-4cc2-8cbb-d16e2f0939b3
-- title:
--   Original norm scalar product le
-- statement:
--   For $\nu\ge0$ and $H>0$, the original scalar product norm is bounded by the exponential of the source weight difference and translation-error budget. All binders, finite domains and hypotheses are precisely the accompanying original formal statement.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

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

theorem OAI.PiExponent.LiteralAnalytic.norm_scalar_product_le {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (f : ChoiceFamily d H) :
    ‖∏ r, choiceScalar d r (f r)‖ ≤ Real.exp
      (-nu * ((∑ r, indexWeight d (f r).1) - (actualRowCount d H : ℝ) * H * actualMean d H) +
        (actualRowCount d H : ℝ) * H * d.translationError) := by
  sorry
