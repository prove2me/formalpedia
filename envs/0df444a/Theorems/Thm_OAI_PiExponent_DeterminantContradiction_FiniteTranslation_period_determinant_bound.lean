-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_period_determinant_bound
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.period_determinant_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:25:05.031101+00:00
-- url     : https://prove2.me/theorems/5e483ac8-7603-4f3c-8061-033d300d33bd
-- title:
--   Period coefficient determinant bound retaining collision multiplicities
-- statement:
--   The formal period coefficient determinant gains the square-multiplicity collision saving, with the exact holomorphic and finite-row collision allowances.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.period_determinant_bound
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : Family d H) :
    ‖(coefficientMatrix d selection f).det‖ ≤
      Real.exp (-collisionConstant *
        (∑ a : Index d H,
          (((Finset.univ : Finset (Row d H)).filter
            (fun r => (f r).1 = a)).card : ℝ) ^ 2) +
        (actualRowCount d H : ℝ) * H *
          (d.holomorphicError + collisionAllowance (actualRowCount d H) H)) := by sorry
