-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_uniform_exp_bound
-- name    : OAI.PiExponent.DeterminantContradiction.actual_minor_uniform_exp_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-07T19:42:03.998127+00:00
-- url     : https://prove2.me/theorems/5c1bf3a1-b882-42ee-8bc3-4ede8ba9371f
-- title:
--   Uniform exponential bound for every actual selected pi minor
-- statement:
--   Fix a real exponent $\nu\ge0$ and an admissible family $d$. Let $M(H)$ be its row count, $b_d(H)$ its mean row weight, $c_d(H)$ its collision rate, and $\varepsilon_d(H)$ the explicit collision and translation error. At every positive height, every selected minor satisfies
--
--   $$\|\det M_d(H)[u]\|\le\exp\left(M(H)H\left[e_{\rm an}(d)+\varepsilon_d(H)+\max\{-c_d(H),-\nu(A(1-\eta)-b_d(H))\}\right]\right).$$
--
--   The estimate is uniform over all selections, including selections with zero determinant. This is an open bridge obligation for the actual truncated logarithmic matrix. The pinned source's formal period collision and translated summand estimates motivate its constants, but do not by themselves establish this actual-matrix statement. It supplies the finite-height analytic input needed for the aggregate reduction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_AnalyticRemainder

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.DeterminantContradiction.actual_minor_uniform_exp_bound
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H) :
    ‖(actualMinor d H selection).det‖ ≤
      Real.exp ((actualRowCount d H : ℝ) * H *
        (d.analyticError + analyticRemainder d H +
          max (-collisionRate d H)
            (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)))) := by sorry
