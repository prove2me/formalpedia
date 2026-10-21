-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_periodMonomial_coeff_eq_series_core
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.periodMonomial_coeff_eq_series_core
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T12:33:47.368063+00:00
-- url     : https://prove2.me/theorems/dcc2c297-4148-4ee5-aedb-7f2e8fc52595
-- title:
--   Power series identity for period monomial coefficients
-- statement:
--   The multivariate coefficient of a period monomial equals the product of its coordinatewise binomial scalar, the outer power-series factor, and the logarithmic series raised to the sum of coordinatewise exponent differences.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms

open scoped BigOperators Topology
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.periodMonomial_coeff_eq_series_core
    {m : ℕ} (j h : ℕ) (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    (periodMonomial j h a).coeff A =
      PowerSeries.C ((∏ i, (a i).choose (A i) : ℕ) : ℂ) *
        (1 + PowerSeries.X) ^ h *
        (PowerSeries.C ((j : ℂ) *
          OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period) +
          PowerSeries.log ℂ) ^
          (∑ i : Fin m, (a i - A i)) := by sorry
