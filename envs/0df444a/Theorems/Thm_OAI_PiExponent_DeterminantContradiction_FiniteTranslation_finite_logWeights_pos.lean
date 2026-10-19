-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_finite_logWeights_pos
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.finite_logWeights_pos
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T13:11:54.820267+00:00
-- url     : https://prove2.me/theorems/0aa2ab88-99f6-46de-bfd8-d21590fcaf8e
-- title:
--   Finite denominator log weights are positive
-- statement:
--   Every log weight associated with a finite denominator in admissible fixed data is positive.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.finite_logWeights_pos
    {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by sorry
