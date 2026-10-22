-- Prove2me | Theorems.Thm_MatrixAnalytic_BirthDeath_limit_prob_ratio
-- name    : MatrixAnalytic.BirthDeath.limit_prob_ratio
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:47.482201+00:00
-- url     : https://prove2.me/theorems/c4d56c8a-d353-4f00-99c2-05b9d6fc1718
-- title:
--   Theorem 4.2.1 — π_n = π_{n−1}R_n, and positive recurrence iff Σ R₁⋯R_k converges
-- statement:
--   Let $P$ be the transition matrix (4.5) of an irreducible, aperiodic birth-and-death chain on $\{0,1,2,\dots\}$, and let $\pi_n=\lim_{k\to\infty}\mathrm P[X_k=n]$ be its limit probabilities. For $n\ge1$ let $R_n$ be the expected total number of visits to state $n$ between two successive visits to $n-1$. Then:
--
--   1. the limit probabilities satisfy
--   $$\pi_n=\pi_{n-1}R_n\qquad\text{for all }n\ge1;$$
--   2. the chain is positive recurrent if and only if the series $\sum_{k\ge1}R_1R_2\cdots R_k$ converges;
--   3. in that case
--   $$\pi_0=\Big(1+\sum_{k\ge1}R_1R_2\cdots R_k\Big)^{-1}.$$
--
--   The theorem expresses the stationary behaviour of the chain through the expected-visit quantities $R_n$, the scalar prototype of the matrix-geometric form studied later in the book.
--
--   **Formalization Note** The limit probabilities are given as a vector $\pi$ with $P^k(0,n)\to\pi_n$ for every $n$ (the chain started in $0$; the book notes the limit does not depend on the initial state). Positive recurrence is stated at state $0$. $R_n$ is the sum over $k\ge1$ of the taboo path sums $r_n(k)$. The series is written $\sum_{k\ge0}\prod_{i=0}^{k}R_{i+1}$, and its convergence is `Summable`.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 89, Theorem 4.2.1

import Mathlib
import Definitions.Def_MatrixAnalytic_BirthDeath_Chain
import Definitions.Def_MatrixAnalytic_BirthDeath_Model
import Definitions.Def_MatrixAnalytic_BirthDeath_Passage

namespace MatrixAnalytic.BirthDeath

theorem limit_prob_ratio (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (hap : AperiodicC P)
    (π : ℕ → ℝ)
    (hπ : ∀ n : ℕ, Filter.Tendsto (fun k : ℕ => stepPow P k 0 n) Filter.atTop (nhds (π n))) :
    (∀ n : ℕ, π (n + 1) = π n * R P (n + 1)) ∧
    (PositiveRecurrent P 0 ↔
      Summable (fun k : ℕ => ∏ i ∈ Finset.range (k + 1), R P (i + 1))) ∧
    (PositiveRecurrent P 0 →
      π 0 = (1 + ∑' k : ℕ, ∏ i ∈ Finset.range (k + 1), R P (i + 1))⁻¹) := by sorry

end MatrixAnalytic.BirthDeath
