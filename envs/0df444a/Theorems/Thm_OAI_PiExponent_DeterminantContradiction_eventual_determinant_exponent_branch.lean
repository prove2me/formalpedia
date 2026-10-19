-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_determinant_exponent_branch
-- name    : OAI.PiExponent.DeterminantContradiction.eventual_determinant_exponent_branch
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T22:13:07.590589+00:00
-- url     : https://prove2.me/theorems/7eb948a5-8844-4514-8105-07d7d676439e
-- title:
--   Eventual exponent branch of the determinant budget gap
-- statement:
--   Eventually, the analytic error and remainder together with the negative exponent-weighted mean gap are strictly below the arithmetic threshold.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem OAI.PiExponent.DeterminantContradiction.eventual_determinant_exponent_branch
    {nu : ℝ} (d : FixedData nu) (hnu : 2 < nu) :
    ∀ᶠ H : ℝ in atTop,
      d.analyticError + analyticRemainder d H +
          (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)) <
        -(1 - actualMean d H) - d.arithmeticError := by sorry
