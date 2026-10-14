-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_low_transverse_capacity
-- name    : OAI.PiExponent.LiteralAnalytic.low_transverse_capacity
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-11T21:55:44.846921+00:00
-- url     : https://prove2.me/theorems/5f4f5d9b-d2e7-4d23-a501-08cf61e38437
-- title:
--   Original low transverse capacity
-- statement:
--   The number of transverse indices of weight at most $d.A\,H$ is at most $lowIndexCount_d(H)$. All binders, finite domains and hypotheses are precisely the accompanying original formal statement.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L133-L153

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

theorem OAI.PiExponent.LiteralAnalytic.low_transverse_capacity {nu : ℝ} (d : FixedData nu) (H : ℝ) :
    (((Finset.univ : Finset (Transverse d H)).filter
      (fun A => indexWeight d A ≤ (d.base.A : ℝ) * H)).card : ℝ) ≤ lowIndexCount d H := by
  sorry
