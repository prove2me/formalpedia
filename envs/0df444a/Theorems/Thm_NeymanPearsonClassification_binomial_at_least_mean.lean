-- Prove2me | Theorems.Thm_NeymanPearsonClassification_binomial_at_least_mean
-- name    : NeymanPearsonClassification.binomial_at_least_mean
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:46:39.044802+00:00
-- url     : https://prove2.me/theorems/a56225cf-baef-4b8d-944a-fc54e43b79c8
-- title:
--   Lemma 6.4: a binomial variable reaches its mean with probability at least min(q, 1/4)
-- statement:
--   Let $N$ be a binomial random variable with parameters $n\ge1$ and $0<q\le1/2$. Then
--
--   $$\mathbb P(N\ge nq)\ge q\wedge\tfrac14.$$
--
--   The bound is uniform in $n$, and it is sharp for $n=1$. It drives the second part of Proposition 3.1.
--
--   **Formalization Note** $\mathbb P(N\ge nq)$ is written as the explicit sum $\sum_{nq\le j\le n}\binom nj q^j(1-q)^{n-j}$.
-- source:
--   Rigollet and Tong, Neyman-Pearson classification, convexity and stochastic constraints, arXiv:1102.5750v1 (2011), Section 6.6, Lemma 6.4, p. 20

import Mathlib
import Definitions.Def_NeymanPearsonClassification_Basic

open MeasureTheory ProbabilityTheory

namespace NeymanPearsonClassification

theorem binomial_at_least_mean (n : ℕ) (hn : 1 ≤ n) (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) :
    min q (1 / 4) ≤ binomTail n q (n * q) := by sorry

end NeymanPearsonClassification
