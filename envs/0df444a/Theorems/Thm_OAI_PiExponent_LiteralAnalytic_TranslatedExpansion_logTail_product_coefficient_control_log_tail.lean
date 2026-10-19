-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_logTail_product_coefficient_control_log_tail
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.logTail_product_coefficient_control_log_tail
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T08:16:26.678321+00:00
-- url     : https://prove2.me/theorems/911c64a6-17ad-4bf9-b9b7-8ca51f973953
-- title:
--   Coefficient bounds for a logarithmic tail
-- statement:
--   For positive T, the logarithmic tail obtained by subtracting log from its truncation has zero coefficients in every degree below T, and every coefficient has norm at most one. The strict cutoff leaves the coefficient at degree T in the tail.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Trunc

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.logTail_product_coefficient_control_log_tail
    (T : ℕ) (hT : 1 ≤ T) :
    (∀ n, n < T →
      PowerSeries.coeff n
        ((PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ) -
          PowerSeries.log ℂ) = 0) ∧
    (∀ n, ‖PowerSeries.coeff n
        ((PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ) -
          PowerSeries.log ℂ)‖ ≤ 1) := by sorry
