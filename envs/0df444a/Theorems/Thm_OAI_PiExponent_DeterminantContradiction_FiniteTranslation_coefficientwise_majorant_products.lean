-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_coefficientwise_majorant_products
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.coefficientwise_majorant_products
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T17:55:29.315147+00:00
-- url     : https://prove2.me/theorems/fd6521bd-e234-414d-90ec-eaef6a5e2816
-- title:
--   Coefficientwise majorants bound coefficients of finite products of powers
-- statement:
--   For a finite family of series, if each factor is coefficientwise dominated in norm by its own series with nonnegative real coefficients, then the same domination holds for the coefficient of the corresponding finite product of natural-number powers.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Mathlib.RingTheory.PowerSeries.Basic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.coefficientwise_majorant_products
    {m : ℕ} (C B : Fin m → PowerSeries ℂ)
    (q : Fin m → ℕ) (k : ℕ)
    (hC : ∀ i n, ∃ x : ℝ, 0 ≤ x ∧ PowerSeries.coeff n (C i) = (x : ℂ))
    (hB : ∀ i n, ‖PowerSeries.coeff n (B i)‖ ≤ ‖PowerSeries.coeff n (C i)‖) :
    ‖PowerSeries.coeff k (∏ i : Fin m, B i ^ q i)‖ ≤
      ‖PowerSeries.coeff k (∏ i : Fin m, C i ^ q i)‖ := by sorry
