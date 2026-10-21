-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_coordinate_factor_support
-- name    : OAI.PiExponent.FinitePeriodCollision.coordinate_factor_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:30:58.481641+00:00
-- url     : https://prove2.me/theorems/1ef632e4-993c-41e0-b786-9a25a6ea93a3
-- title:
--   Support of a powered coordinate factor
-- statement:
--   Every monomial with nonzero coefficient in the factor `(C (b i) + X i) ^ a i` uses only variable `i`. This includes exponent zero and the zero-power case.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
open OAI.PiExponent
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.coordinate_factor_support
    {m : ℕ} (a : Fin m → ℕ) (b : Fin m → PowerSeries ℂ) :
    ∀ (i : Fin m) (s : Fin m →₀ ℕ),
      ((MvPolynomial.C (b i) + MvPolynomial.X i) ^ a i).coeff s ≠ 0 →
        ∀ j : Fin m, s j ≠ 0 → j = i := by sorry
