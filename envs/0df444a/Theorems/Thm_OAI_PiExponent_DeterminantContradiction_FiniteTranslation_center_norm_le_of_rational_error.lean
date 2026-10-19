-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_center_norm_le_of_rational_error
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_norm_le_of_rational_error
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T17:29:45.795667+00:00
-- url     : https://prove2.me/theorems/c48ff820-62cf-46be-8759-170e49dff715
-- title:
--   Scaled rational approximation controls the translated-center norm
-- statement:
--   A rational approximation to pi bounds the norm of its translated complex-center error after scaling by an integer at most K.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_norm_le_of_rational_error
    {nu : ℝ} (p : ℤ) (q k K : ℕ) (hnu : 0 ≤ nu)
    (hq : 0 < q) (hk : k ≤ K)
    (herr : |Real.pi - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-nu)) :
    ‖((k : ℂ) *
      (2 * Complex.I * (p : ℂ) / (q : ℂ) -
        2 * (Real.pi : ℂ) * Complex.I))‖ ≤
      2 * (K : ℝ) * (q : ℝ) ^ (-nu) := by sorry
