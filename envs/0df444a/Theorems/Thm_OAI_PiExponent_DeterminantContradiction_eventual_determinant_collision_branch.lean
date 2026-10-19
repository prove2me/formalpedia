-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_determinant_collision_branch
-- name    : OAI.PiExponent.DeterminantContradiction.eventual_determinant_collision_branch
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T22:12:42.728058+00:00
-- url     : https://prove2.me/theorems/f9fcc49e-2e2c-4c36-a525-40b617d83feb
-- title:
--   Eventual collision branch of the determinant budget gap
-- statement:
--   Eventually, the analytic error and remainder together with the negative collision rate are strictly below the arithmetic threshold.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem OAI.PiExponent.DeterminantContradiction.eventual_determinant_collision_branch
    {nu : ℝ} (d : FixedData nu) (hnu : 2 < nu) :
    ∀ᶠ H : ℝ in atTop,
      d.analyticError + analyticRemainder d H + (-collisionRate d H) <
        -(1 - actualMean d H) - d.arithmeticError := by sorry
