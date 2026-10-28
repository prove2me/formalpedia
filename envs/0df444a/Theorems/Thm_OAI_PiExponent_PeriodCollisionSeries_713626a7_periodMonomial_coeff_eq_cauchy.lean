-- Prove2me | Theorems.Thm_OAI_PiExponent_PeriodCollisionSeries_713626a7_periodMonomial_coeff_eq_cauchy
-- name    : OAI.PiExponent.PeriodCollisionSeries_713626a7.periodMonomial_coeff_eq_cauchy
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T18:57:43.248977+00:00
-- url     : https://prove2.me/theorems/b401e0f6-3f2f-4b42-b1cc-56ad56a87cd9
-- title:
--   Formal period coefficient as a composed Cauchy coefficient
-- statement:
--   Expanding the multivariate monomial coefficient gives a binomial-weighted logarithmic power times `(1 + X)^h`; the identity `exp (h * (j * period + log (1+t))) = (1+t)^h` identifies its coefficient with the Cauchy coefficient of the composed `columnFunction`.
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

theorem OAI.PiExponent.PeriodCollisionSeries_713626a7.periodMonomial_coeff_eq_cauchy
    {m : ℕ} (j h ell : ℕ) (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    PowerSeries.coeff ell ((periodMonomial j h a).coeff A) =
      cauchyPowerSeries
        (fun t : ℂ => columnFunction h a A
          ((j : ℂ) * period + Complex.log (1 + t)))
        0 (1 / 2) ell (fun _ => (1 : ℂ)) := by sorry
