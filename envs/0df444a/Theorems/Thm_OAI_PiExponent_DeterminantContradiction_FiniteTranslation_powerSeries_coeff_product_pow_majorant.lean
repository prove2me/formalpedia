-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_powerSeries_coeff_product_pow_majorant
-- name    : OAI.PiExponent.DeterminantContradiction.FiniteTranslation.powerSeries_coeff_product_pow_majorant
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T17:45:32.226391+00:00
-- url     : https://prove2.me/theorems/92539db6-6c10-4720-8380-6c89f0623f90
-- title:
--   Coefficientwise domination passes through finite products and powers
-- statement:
--   If every series in a finite family is coefficientwise bounded in norm by one series with nonnegative real coefficients, then the coefficient of their product of natural-number powers is bounded by the corresponding coefficient of the majorant raised to the sum of those powers. Prove by induction on powers and the finite Cauchy-product formula, applying the triangle inequality and nonnegativity at each convolution.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.powerSeries_coeff_product_pow_majorant
    {m : ℕ} (L : PowerSeries ℂ) (B : Fin m → PowerSeries ℂ)
    (q : Fin m → ℕ) (k : ℕ)
    (hL : ∀ n, ∃ x : ℝ, 0 ≤ x ∧ PowerSeries.coeff n L = (x : ℂ))
    (hB : ∀ i n, ‖PowerSeries.coeff n (B i)‖ ≤ ‖PowerSeries.coeff n L‖) :
    ‖PowerSeries.coeff k (∏ i : Fin m, B i ^ q i)‖ ≤
      ‖PowerSeries.coeff k (L ^ (∑ i : Fin m, q i))‖ := by sorry
