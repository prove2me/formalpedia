-- Prove2me | Theorems.Thm_GreedyRS_Greedy_lemma1_argmin_finite
-- name    : GreedyRS.Greedy.lemma1_argmin_finite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:08.347179+00:00
-- url     : https://prove2.me/theorems/e05387af-45f3-4391-b206-3b7b207c814a
-- title:
--   Lemma 1, p. 13 — the running average of i.i.d. N(0,1) attains its minimum in finite time a.s.
-- statement:
--   Let $Z_1,Z_2,\dots$ be independent standard normal random variables and $\bar Z(n)=\frac1n\sum_{j=1}^nZ_j$ their running average. Then the running-average process $\{\bar Z(n),\,n\ge1\}$ reaches its minimum after finitely many observations almost surely:
--   $$\Pr\Bigl\{\operatorname*{arg\,min}_{n\ge1}\bar Z(n)<\infty\Bigr\}=1.$$
--
--   By the strong law, $\bar Z(n)\to0$, so the claim is that the infimum is attained. Applied to $\bar X_1(n)=\mu_1+\sigma_1\bar Z(n)$, it shows that the best alternative's running average reaches its minimum $N_1^*$ within finite time, so this cost is negligible against a budget linear in $k$.
--
--   **Formalization Note** $\arg\min_{n\ge1}\bar Z(n)$ is the first index $m\ge1$ with $\bar Z(m)\le\bar Z(n)$ for all $n\ge1$, valued in $\mathbb N\cup\{\infty\}$ and equal to $\infty$ if no such index exists. The sequence $Z$ is drawn from the infinite product of $N(0,1)$.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. 13, Lemma 1; proof EC.1.1, p. ec1

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GreedyRS.Greedy
theorem lemma1_argmin_finite :
    ∀ᵐ z ∂stdNormalSeq, argminFrom (zbar z) 1 < ⊤ := by sorry
end GreedyRS.Greedy
