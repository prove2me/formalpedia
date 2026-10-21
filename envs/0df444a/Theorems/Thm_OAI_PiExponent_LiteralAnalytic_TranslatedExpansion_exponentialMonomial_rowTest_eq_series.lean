-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_exponentialMonomial_rowTest_eq_series
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.exponentialMonomial_rowTest_eq_series
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:07:49.32148+00:00
-- url     : https://prove2.me/theorems/e637875a-f5af-41fd-b3ed-9496af4dc40e
-- title:
--   Exponential monomial row test as a power-series coefficient
-- statement:
--   The analytic row test of an exponential monomial centered at the integer period is the corresponding coefficient of its power-series expansion in the logarithmic coordinate.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms

open scoped BigOperators Topology
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.exponentialMonomial_rowTest_eq_series
    (b : ℂ) (j h d ell : ℕ) :
    rowTest ell (fun t => exponentialMonomial b (h : ℂ) d
      ((j : ℂ) * OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period +
        Complex.log (1 + t))) =
    PowerSeries.coeff ell
      (PowerSeries.C b * (1 + PowerSeries.X) ^ h *
        (PowerSeries.C ((j : ℂ) *
          OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period) +
          PowerSeries.log ℂ) ^ d) := by sorry
