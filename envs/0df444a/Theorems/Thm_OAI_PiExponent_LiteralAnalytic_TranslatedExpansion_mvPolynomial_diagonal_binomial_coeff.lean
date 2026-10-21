-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_mvPolynomial_diagonal_binomial_coeff
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.mvPolynomial_diagonal_binomial_coeff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T12:42:20.995277+00:00
-- url     : https://prove2.me/theorems/fbced49b-a0cb-4c83-af14-c0e6e5fd7fd6
-- title:
--   Coefficient formula for diagonal multivariate binomials
-- statement:
--   For any outer power-series scalar and common binomial constant, the coefficient at a finitely supported multivariate exponent is the outer scalar times the product of the coordinatewise binomial coefficients and the common constant raised to the sum of the coordinatewise exponent differences.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms

open scoped BigOperators Topology
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.mvPolynomial_diagonal_binomial_coeff
    {m : ℕ} (u s : PowerSeries ℂ) (a : Fin m → ℕ)
    (A : Fin m →₀ ℕ) :
    (MvPolynomial.C u *
      ∏ i : Fin m, (MvPolynomial.C s + MvPolynomial.X i) ^ a i).coeff A =
      u * PowerSeries.C ((∏ i, (a i).choose (A i) : ℕ) : ℂ) *
        s ^ (∑ i : Fin m, (a i - A i)) := by sorry
