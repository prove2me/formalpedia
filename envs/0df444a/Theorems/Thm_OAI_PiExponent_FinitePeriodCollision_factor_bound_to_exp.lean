-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_factor_bound_to_exp
-- name    : OAI.PiExponent.FinitePeriodCollision.factor_bound_to_exp
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T23:08:19.663129+00:00
-- url     : https://prove2.me/theorems/d1be2bde-0e2c-4139-9af9-9dd1da13a62a
-- title:
--   Normalize finite collision factors with the exact row allowance
-- statement:
--   For any finite grouping and nonnegative integer derivative orders whose total is at most MH/v, the factorial and geometric collision factors are bounded by the exponential containing the negative squared multiplicities and the exact collision allowance.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.FinitePeriodCollision.factor_bound_to_exp
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (ell : ι → ℕ) {H A v : ℝ}
    (hH : 0 < H) (hv : 0 < v)
    (hell : ((∑ r, ell r : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v) :
    (((Fintype.card ι).factorial : ℝ) *
        (Real.exp (H * A)) ^ Fintype.card ι * (2 : ℝ) ^ (∑ r, ell r)) *
      (Real.exp (-Real.log 2 / 2)) ^
        (∑ b : κ, (((Finset.univ : Finset ι).filter (fun r => group r = b)).card).choose 2) *
      ((1 - Real.exp (-Real.log 2 / 2))⁻¹) ^ Fintype.card ι ≤
    Real.exp (-(Real.log 2 / 4) *
      (∑ b : κ, ((((Finset.univ : Finset ι).filter
        (fun r => group r = b)).card : ℝ) ^ 2)) +
      (Fintype.card ι : ℝ) * H *
        (A + Real.log 2 / v + collisionAllowance (Fintype.card ι) H)) := by sorry
