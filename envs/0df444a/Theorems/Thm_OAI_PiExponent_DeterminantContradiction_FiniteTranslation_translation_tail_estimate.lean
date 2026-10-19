-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_translation_tail_estimate
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_tail_estimate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-18T13:35:50.021345+00:00
-- url     : https://prove2.me/theorems/56bb77dd-2a69-4b15-a9f9-0d4fec6f41ee
-- title:
--   Binomial and truncated-log tail estimate
-- statement:
--   Bound the product of the binomial prefactor and the coefficient of the truncated-log tail powers by the remaining translation allowance. This removes the coefficient estimate from the parent while keeping the exact truncation orders and coefficient index. A proof route expands the power-series coefficient, uses that truncation at `T` keeps degrees strictly below `T` (so the tail starts at degree `T`), then applies the finite choice bounds, the `FixedData` logarithmic denominator data, and the `wstar` bounds. The coefficient cutoff and binomial growth are the main remaining work; this is not a restatement of the parent scalar inequality.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_tail_estimate
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r) :
    ‖(((∏ i : Fin d.m,
          (t.1.1 i).choose (r.2.1 i.succ) *
            (t.1.1 i - r.2.1 i.succ).choose (t.2.1 i) : ℕ) : ℂ) *
      PowerSeries.coeff (t.2.2 : ℕ)
        (∏ i : Fin d.m,
          ((PowerSeries.trunc
            (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
            (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ) ^
              (t.2.1 i : ℕ)))‖ ≤
      Real.exp
        (H * ((Real.log 4 + Real.log (2 * (d.K : ℝ)) + nu) / d.wstar)) := by sorry
