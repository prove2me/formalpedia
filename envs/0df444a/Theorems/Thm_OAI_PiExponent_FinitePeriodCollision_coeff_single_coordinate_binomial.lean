-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_coeff_single_coordinate_binomial
-- name    : OAI.PiExponent.FinitePeriodCollision.coeff_single_coordinate_binomial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:27:23.467693+00:00
-- url     : https://prove2.me/theorems/1b97c74e-fc1c-4b81-b459-719a44f6e761
-- title:
--   Coefficient of a one-coordinate binomial power
-- statement:
--   For one coordinate, the coefficient of exponent $k$ in $(b_i+X_i)^n$ is the usual binomial coefficient times the remaining constant-term power, embedded as a constant power series.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.coeff_single_coordinate_binomial
    {m : ℕ} (i : Fin m) (n k : ℕ) (b : Fin m → PowerSeries ℂ) :
    ((MvPolynomial.C (b i) + MvPolynomial.X i) ^ n).coeff
        (Finsupp.single i k) =
      PowerSeries.C (((n.choose k : ℕ) : ℂ)) * b i ^ (n - k) := by sorry
