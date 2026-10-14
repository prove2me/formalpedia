-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_entry_row_choice_expansion
-- name    : OAI.PiExponent.LiteralAnalytic.actual_entry_row_choice_expansion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T09:10:46.728476+00:00
-- url     : https://prove2.me/theorems/07482ec6-59a3-42ea-9743-0741c15c1590
-- title:
--   Finite translation-choice expansion of an actual matrix entry
-- statement:
--   For any actual row and column, the matrix entry equals the finite sum over that row’s translation choices. Each contribution multiplies its row scalar by the period-monomial coefficient at the remaining power-series order s−k.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticAggregate.lean#L12-L33

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.LiteralAnalytic.actual_entry_row_choice_expansion
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (r : Row d H) (c : Column d H) :
    actualMatrix d H r c =
      ∑ t : RowChoice d H r, choiceScalar d r t *
        PowerSeries.coeff (r.2.1 0 - t.2.2)
          ((MatrixTranslation.periodMonomial r.1.val logarithmicPeriod
            (c.1 0) (fun i => c.1 i.succ)).coeff t.1.1) := by
  sorry
