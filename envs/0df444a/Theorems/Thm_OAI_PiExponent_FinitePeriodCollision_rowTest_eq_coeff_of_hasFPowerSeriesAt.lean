-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_rowTest_eq_coeff_of_hasFPowerSeriesAt
-- name    : OAI.PiExponent.FinitePeriodCollision.rowTest_eq_coeff_of_hasFPowerSeriesAt
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T13:09:25.487128+00:00
-- url     : https://prove2.me/theorems/a0f3752d-185d-4109-b8c7-4dd46012010a
-- title:
--   Cauchy row tests recover coefficients of a local formal series
-- statement:
--   If a complex-valued function is differentiable on the closed radius-`1/2` disk and has at zero the scalar formal series associated to `s`, then its normalized radius-`1/2` Cauchy row test is the `ell`th coefficient of `s`. This removes the Cauchy integral and formal-series uniqueness argument from the parent. An independent proof route is to construct the Cauchy power series on the disk from differentiability, identify its formal multilinear series at zero with the supplied one using `HasFPowerSeriesAt.eq_formalMultilinearSeries`, and evaluate both series at the `ell`th index and the constant vector `1`. This route works at `ell = 0` as well.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Mathlib.Analysis.Complex.CauchyIntegral

theorem OAI.PiExponent.FinitePeriodCollision.rowTest_eq_coeff_of_hasFPowerSeriesAt
    (ell : ℕ) (f : ℂ → ℂ) (s : PowerSeries ℂ)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 (1 / 2)))
    (hp : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff n s)) 0) :
    rowTest ell f = PowerSeries.coeff ell s := by sorry
