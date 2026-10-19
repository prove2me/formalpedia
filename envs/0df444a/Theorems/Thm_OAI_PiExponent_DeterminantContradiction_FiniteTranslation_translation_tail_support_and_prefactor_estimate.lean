-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_translation_tail_support_and_prefactor_estimate
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_tail_support_and_prefactor_estimate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T17:13:15.237597+00:00
-- url     : https://prove2.me/theorems/b7dd2d56-47cf-402b-be39-8527f8b3e554
-- title:
--   Nonzero logarithmic tail support and binomial-prefactor bound
-- statement:
--   A nonzero tail coefficient forces its degree to be at least the sum of the truncation orders multiplied by their powers. Composition counting bounds the coefficient, and binomial estimates bound its prefactor. The support inequality allows equality at the truncation cutoff; the parent handles zero coefficients separately.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_tail_support_and_prefactor_estimate
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r)
    (hne : PowerSeries.coeff (t.2.2 : ℕ)
      (∏ i : Fin d.m,
        ((PowerSeries.trunc
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
          (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ) ^
            (t.2.1 i : ℕ)) ≠ 0) :
    ((∑ i : Fin d.m,
      MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i *
        (t.2.1 i : ℕ)) ≤ (t.2.2 : ℕ)) ∧
    ‖(((∏ i : Fin d.m,
          (t.1.1 i).choose (r.2.1 i.succ) *
            (t.1.1 i - r.2.1 i.succ).choose (t.2.1 i) : ℕ) : ℂ) *
      PowerSeries.coeff (t.2.2 : ℕ)
        (∏ i : Fin d.m,
          ((PowerSeries.trunc
            (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
            (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ) ^
              (t.2.1 i : ℕ)))‖ ≤
      Real.exp (H * (Real.log 4 / d.wstar + Real.log 2 / (d.v0 : ℝ))) := by sorry
