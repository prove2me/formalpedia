-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowWeight_le_indexWeight_of_ne_zero
-- name    : OAI.PiExponent.LiteralAnalytic.rowWeight_le_indexWeight_of_ne_zero
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-11T21:56:24.03652+00:00
-- url     : https://prove2.me/theorems/3ab7fc0d-2a1e-475f-94b6-458d53be7579
-- title:
--   Original rowWeight le indexWeight of ne zero
-- statement:
--   If the original scalar for row $r$ and row choice $t$ is nonzero, then $rowWeight_d(r)\le indexWeight_d(t.1)$. All binders, finite domains and hypotheses are precisely the accompanying original formal statement.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L109-L115

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

theorem OAI.PiExponent.LiteralAnalytic.rowWeight_le_indexWeight_of_ne_zero {nu : ℝ} (d : FixedData nu)
    {H : ℝ} (r : Row d H) (t : RowChoice d H r) (ht : choiceScalar d r t ≠ 0) :
    rowWeight d r ≤ indexWeight d t.1 := by
  sorry
