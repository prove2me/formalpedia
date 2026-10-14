-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_indexWeight_nonneg
-- name    : OAI.PiExponent.LiteralAnalytic.indexWeight_nonneg
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-11T21:57:14.895825+00:00
-- url     : https://prove2.me/theorems/0aeabe86-ff79-46b4-b8e3-eacc0125c4e4
-- title:
--   Original indexWeight nonneg
-- statement:
--   Each transverse index has nonnegative weight: $indexWeight_d(a)\ge0$. All binders, finite domains and hypotheses are precisely the accompanying original formal statement.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L70-L73

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

theorem OAI.PiExponent.LiteralAnalytic.indexWeight_nonneg {nu : ℝ} (d : FixedData nu) {H : ℝ} (a : Transverse d H) :
    0 ≤ indexWeight d a := by
  sorry
