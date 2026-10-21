-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_periodMonomial_coeff_eq_rowTest
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.periodMonomial_coeff_eq_rowTest
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T07:52:17.143419+00:00
-- url     : https://prove2.me/theorems/9e5eff4e-dccd-4e6a-8190-46a7e62183c2
-- title:
--   Period-monomial coefficients as analytic row tests
-- statement:
--   The coefficient of a period monomial at a multivariate exponent is the analytic row test of an exponential monomial. Its scalar is the product of binomial coefficients, and its exponential degree is the sum of the coordinatewise exponent differences.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms

open scoped BigOperators Topology
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.periodMonomial_coeff_eq_rowTest
    {m : ℕ} (j h ell : ℕ) (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    PowerSeries.coeff ell
      ((periodMonomial j h a).coeff A) =
    rowTest ell (fun t => exponentialMonomial
      ((∏ i, (a i).choose (A i) : ℕ) : ℂ) (h : ℂ)
      (∑ i : Fin m, (a i - A i))
      ((j : ℂ) * OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period +
        Complex.log (1 + t))) := by sorry
