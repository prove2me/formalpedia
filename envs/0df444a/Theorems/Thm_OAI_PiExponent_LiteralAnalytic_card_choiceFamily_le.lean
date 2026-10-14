-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_card_choiceFamily_le
-- name    : OAI.PiExponent.LiteralAnalytic.card_choiceFamily_le
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-11T22:01:06.118682+00:00
-- url     : https://prove2.me/theorems/c87f22ee-147d-4136-86b5-b2aa40de33bf
-- title:
--   Original card choiceFamily le
-- statement:
--   The number of choice families is at most $translationTermCount(d.m,d.v_0,H)^{actualRowCount_d(H)}$ under the exact source hypotheses. All binders, finite domains and hypotheses are precisely the accompanying original formal statement.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticAggregate.lean#L35-L47

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

theorem OAI.PiExponent.LiteralAnalytic.card_choiceFamily_le {nu : ℝ} (d : FixedData nu) (H : ℝ) :
    Fintype.card (ChoiceFamily d H) ≤ translationTermCount d.m d.v0 H ^ actualRowCount d H := by
  sorry
