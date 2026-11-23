-- Prove2me | Theorems.Thm_NeymanPearsonClassification_binomial_lower_tail
-- name    : NeymanPearsonClassification.binomial_lower_tail
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:45:33.514181+00:00
-- url     : https://prove2.me/theorems/9f87280f-1a93-4703-8d25-d450c198f58f
-- title:
--   Lemma 6.3: lower tail bound for the binomial distribution
-- statement:
--   Let $N$ be a binomial random variable with parameters $n\ge1$ and $q\in(0,1)$. Then for every $t>0$ with $t\le nq/2$,
--
--   $$\mathbb P(N\ge t)\ge1-e^{-nq^2/2}.$$
--
--   It controls the random class sizes $N^-$ and $N^+$ in Corollary 4.1.
--
--   **Formalization Note** $\mathbb P(N\ge t)$ is written as the explicit sum $\sum_{t\le j\le n}\binom nj q^j(1-q)^{n-j}$.
-- source:
--   Rigollet and Tong, Neyman-Pearson classification, convexity and stochastic constraints, arXiv:1102.5750v1 (2011), Section 6.6, Lemma 6.3, p. 19

import Mathlib
import Definitions.Def_NeymanPearsonClassification_Basic

open MeasureTheory ProbabilityTheory

namespace NeymanPearsonClassification

theorem binomial_lower_tail (n : ℕ) (hn : 1 ≤ n) (q : ℝ) (hq : q ∈ Set.Ioo 0 1)
    (t : ℝ) (ht : 0 < t) (htq : t ≤ n * q / 2) :
    1 - Real.exp (-(n * q ^ 2 / 2)) ≤ binomTail n q t := by sorry

end NeymanPearsonClassification
