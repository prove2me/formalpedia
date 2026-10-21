-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_determinant_budget_gap
-- name    : OAI.PiExponent.DeterminantContradiction.eventual_determinant_budget_gap
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T22:07:24.49524+00:00
-- url     : https://prove2.me/theorems/21483e8e-daef-46c8-b153-9cd92f88be08
-- title:
--   Eventual strict gap between analytic budget and arithmetic threshold
-- statement:
--   For every admissible datum of exponent greater than two, at all sufficiently large real heights the analytic determinant budget is strictly below the arithmetic lower threshold. This scalar asymptotic comparison uses the strict parameter margins, mean-row-weight bounds, the vanishing analytic remainder, and the collision-rate limit.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem OAI.PiExponent.DeterminantContradiction.eventual_determinant_budget_gap
    {nu : ℝ} (d : FixedData nu) (hnu : 2 < nu) :
    ∀ᶠ H : ℝ in atTop,
      d.analyticError + analyticRemainder d H +
          max (-collisionRate d H)
            (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)) <
        -(1 - actualMean d H) - d.arithmeticError := by sorry
