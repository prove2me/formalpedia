-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_translated_row_expansion
-- name    : OAI.PiExponent.FinitePeriodCollision.translated_row_expansion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:13:19.505706+00:00
-- url     : https://prove2.me/theorems/44fed52f-b89d-47c0-8ec4-1e2b9bf19150
-- title:
--   Taylor expansion after the logarithmic row test
-- statement:
--   For a differentiable function bounded on the radius-`R` circle, expand its value at each logarithmically translated test point in normalized Taylor coefficients and pass the convergent sum through `rowTest`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic

open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.translated_row_expansion
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (R : NNReal) (hR : 0 < R) (D : ℝ) (hD : 0 ≤ D)
    (hfD : ∀ z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) → ‖f z‖ ≤ D)
    (center : ℂ) (hc : ‖center‖ + 3 / 4 ≤ (R : ℝ) / 2) (ell : ℕ) :
    HasSum
      (fun d =>
        rowTest ell
          (fun t => ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d) *
          cauchyPowerSeries f 0 (R : ℝ) d (fun _ => (R : ℂ)))
      (rowTest ell (fun t => f (center + Complex.log (1 + t)))) := by sorry
