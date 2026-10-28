-- Prove2me | Theorems.Thm_OAI_PiExponent_PeriodCollisionSeries_713626a7_cauchy_composition_hasSum
-- name    : OAI.PiExponent.PeriodCollisionSeries_713626a7.cauchy_composition_hasSum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T18:57:22.698108+00:00
-- url     : https://prove2.me/theorems/62c3c7ec-9817-4972-927c-5edba8e6541b
-- title:
--   Cauchy coefficient transfer through a translated logarithm
-- statement:
--   For an entire function, the Cauchy coefficient of its composition with the translated logarithm is the sum of products of the logarithm's normalized Cauchy coefficients and the function's radius-scaled Taylor coefficients.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.PeriodCollisionSeries_713626a7.cauchy_composition_hasSum
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (R : ℝ) (hR : 0 < R)
    (center : ℂ) (hc : ‖center‖ + 3 / 4 ≤ R / 2) (ell : ℕ) :
    HasSum
      (fun d : ℕ =>
        cauchyPowerSeries
            (fun t : ℂ => (((center + Complex.log (1 + t)) / (R : ℂ)) ^ d))
            0 (1 / 2) ell (fun _ => (1 : ℂ)) *
          cauchyPowerSeries f 0 R d (fun _ => (R : ℂ)))
      (cauchyPowerSeries (fun t : ℂ => f (center + Complex.log (1 + t)))
        0 (1 / 2) ell (fun _ => (1 : ℂ))) := by sorry
