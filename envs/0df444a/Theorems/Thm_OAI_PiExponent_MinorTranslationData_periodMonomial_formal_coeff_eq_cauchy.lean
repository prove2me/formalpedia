-- Prove2me | Theorems.Thm_OAI_PiExponent_MinorTranslationData_periodMonomial_formal_coeff_eq_cauchy
-- name    : OAI.PiExponent.MinorTranslationData.periodMonomial_formal_coeff_eq_cauchy
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:55:18.539001+00:00
-- url     : https://prove2.me/theorems/8c03801b-68f9-4fd0-8d88-870ad08f40a8
-- title:
--   Identifying the formal series coefficient with its Cauchy coefficient
-- statement:
--   The coefficient of the extracted formal series equals the Cauchy coefficient of the analytic expression. Prove it by establishing the analytic power-series representation on the radius-`1/2` disk: rewrite the exponential using integer-periodicity, use the convergent logarithm series there, and identify the representing series with `cauchyPowerSeries`.

import Definitions.Def_OAI_PiExponent_MinorTranslationData
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.MinorTranslationData.periodMonomial_formal_coeff_eq_cauchy
    {m : ℕ} (j h ell : ℕ) (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    PowerSeries.coeff ell
        (PowerSeries.C ((∏ i, (a i).choose (A i) : ℕ) : ℂ) *
          (PowerSeries.C ((j : ℂ) * period) + PowerSeries.log ℂ) ^
            (∑ i : Fin m, (a i - A i)) *
          (1 + PowerSeries.X) ^ h) =
      cauchyPowerSeries
        (fun t : ℂ =>
          ((∏ i, (a i).choose (A i) : ℕ) : ℂ) *
            Complex.exp ((h : ℂ) * ((j : ℂ) * period + Complex.log (1 + t))) *
            ((j : ℂ) * period + Complex.log (1 + t)) ^
              (∑ i : Fin m, (a i - A i)))
        0 (1 / 2) ell (fun _ => (1 : ℂ)) := by sorry
