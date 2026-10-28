-- Prove2me | Theorems.Thm_OAI_PiExponent_PeriodCollisionSeries_713626a7_periodMonomial_coeff_eq_formal
-- name    : OAI.PiExponent.PeriodCollisionSeries_713626a7.periodMonomial_coeff_eq_formal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T19:07:09.500418+00:00
-- url     : https://prove2.me/theorems/2f36abb2-527f-4a83-bec1-01b2a5832a5e
-- title:
--   Extracting the formal period monomial coefficient
-- statement:
--   The multivariate coefficient equals the product of coordinate binomial coefficients times the coefficient of the translated logarithmic series raised to the sum of the coordinatewise truncated differences.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_PeriodCollisionSeries_713626a7
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log

open OAI.PiExponent
open OAI.PiExponent.FiniteMinorAnalysis_690acb6f
open OAI.PiExponent.PeriodCollisionSeries_713626a7
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.PeriodCollisionSeries_713626a7.periodMonomial_coeff_eq_formal {m : ℕ} (j h ell : ℕ) (a : Fin m → ℕ) (A : Fin m →₀ ℕ) : PowerSeries.coeff ell ((periodMonomial j h a).coeff A) = ((Finset.univ.prod (fun i : Fin m => (a i).choose (A i)) : ℕ) : ℂ) * PowerSeries.coeff ell ((1 + PowerSeries.X) ^ h * (PowerSeries.C ((j : ℂ) * FiniteMinorAnalysis_690acb6f.period) + PowerSeries.log ℂ) ^ (Finset.univ.sum (fun i : Fin m => a i - A i))) := by sorry
