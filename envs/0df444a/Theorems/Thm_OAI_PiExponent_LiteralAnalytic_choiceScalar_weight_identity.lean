-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_choiceScalar_weight_identity
-- name    : OAI.PiExponent.LiteralAnalytic.choiceScalar_weight_identity
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T11:51:28.616612+00:00
-- url     : https://prove2.me/theorems/f2539a12-ec84-432e-8301-ec8f721dab1c
-- title:
--   Coordinate sum identity for row and index weights
-- statement:
--   The finite sum of coordinate weight differences for the selected multi-index equals the difference between its index weight and the row weight. This is a definition-level identity, independent of the analytic estimate.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

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

theorem OAI.PiExponent.LiteralAnalytic.choiceScalar_weight_identity {nu : ℝ} (d : FixedData nu)
    {H : ℝ} (r : Row d H) (t : RowChoice d H r) :
    ∑ i : Fin d.m, fixedWeights d i *
        ((t.1.1 i : ℝ) - (beta d r i : ℝ)) =
      indexWeight d t.1 - rowWeight d r := by sorry
