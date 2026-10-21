-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_CollisionAnalytic_hasSum_cauchy_translated_row
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic.hasSum_cauchy_translated_row
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T18:07:35.466837+00:00
-- url     : https://prove2.me/theorems/5afb9396-b723-40d7-b3e7-90c559c7b8d9
-- title:
--   Cauchy-series expansion of a translated logarithmic row test
-- statement:
--   An entire function bounded by a nonnegative D on the positive-radius R sphere has a translated logarithmic row test equal to the convergent sum of normalized Cauchy coefficients times row tests of normalized shifted powers, under the stated center inequality.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers

open scoped BigOperators Topology
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic.hasSum_cauchy_translated_row
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (R : NNReal) (hR : 0 < R) (D : ℝ) (hD : 0 ≤ D)
    (hfD : ∀ z ∈ Metric.sphere (0 : ℂ) (R : ℝ), ‖f z‖ ≤ D)
    (center : ℂ) (hc : ‖center‖ + 3 / 4 ≤ (R : ℝ) / 2) (ell : ℕ) :
    HasSum (fun d =>
      rowTest ell (fun t => ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d) *
        cauchyPowerSeries f 0 (R : ℝ) d (fun _ => (R : ℂ)))
      (rowTest ell (fun t => f (center + Complex.log (1 + t)))) := by sorry
