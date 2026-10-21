-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_hasFPowerSeriesAt_periodFunction
-- name    : OAI.PiExponent.FinitePeriodCollision.hasFPowerSeriesAt_periodFunction
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T13:09:10.338625+00:00
-- url     : https://prove2.me/theorems/daa8517e-9760-461c-9bb3-e1ff149f9da8
-- title:
--   The period function has its formal Taylor series at zero
-- statement:
--   For arbitrary complex b and center and natural h and d, the indicated period function has at zero the formal multilinear series whose scalar coefficients are those of the displayed PowerSeries product. This isolates the logarithm series and formal-series multiplication and power calculations from the Cauchy coefficient step. The independent proof route in the pinned upstream source is to establish `HasSum` for the coefficients of constants, `X`, and the formal logarithm on `‖t‖ < 1`, combine these with the coefficient-series product and power lemmas, and convert the resulting local `HasSum` statement to `HasFPowerSeriesAt`. The zero exponents require no extra hypotheses: the corresponding formal powers are the unit series.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

theorem OAI.PiExponent.FinitePeriodCollision.hasFPowerSeriesAt_periodFunction
    (b center : ℂ) (h d : ℕ) :
    HasFPowerSeriesAt
      (fun t : ℂ => b * (1 + t) ^ h * (center + Complex.log (1 + t)) ^ d)
      (FormalMultilinearSeries.ofScalars ℂ (fun n =>
        PowerSeries.coeff n
          (PowerSeries.C b * (1 + PowerSeries.X) ^ h *
            (PowerSeries.C center + PowerSeries.log ℂ) ^ d))) 0 := by sorry
