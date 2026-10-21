-- Prove2me | Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_singleCoordinatePolynomialCoeff
-- name    : OAI.PiExponent.FinitePeriodCollision.singleCoordinatePolynomialCoeff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:32:29.601102+00:00
-- url     : https://prove2.me/theorems/bc8672bf-8fa6-4fcc-aed8-d1cabcd86d20
-- title:
--   Coefficient preservation for a single-variable polynomial evaluation
-- statement:
--   Evaluating a univariate polynomial over power series at the multivariate variable `X i`, while embedding coefficients as constants, preserves its `k`th coefficient at multidegree `Finsupp.single i k`. The lemma holds for every coordinate and degree, including degree zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Mathlib.Algebra.Polynomial.Coeff

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.singleCoordinatePolynomialCoeff
    {m : ℕ} (i : Fin m) (p : Polynomial (PowerSeries ℂ)) (k : ℕ) :
    (Polynomial.eval₂
        (MvPolynomial.C : PowerSeries ℂ →+* MvPolynomial (Fin m) (PowerSeries ℂ))
        (MvPolynomial.X i) p).coeff (Finsupp.single i k) = p.coeff k := by sorry
