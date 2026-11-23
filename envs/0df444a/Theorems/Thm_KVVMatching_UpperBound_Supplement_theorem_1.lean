-- Prove2me | Theorems.Thm_KVVMatching_UpperBound_Supplement_theorem_1
-- name    : KVVMatching.UpperBound.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:49:59.271333+00:00
-- url     : https://prove2.me/theorems/fe8bbc2c-e151-4781-8fa7-f17a52fcd3b5
-- title:
--   Theorem 1 — the performance of EARLY on upper-triangular matrices is n(1 − 1/e) + o(n)
-- statement:
--   Let $B$ be an $n\times n$ $0/1$ matrix whose rows are the boys and whose columns are the girls of a bipartite graph. Throughout the analysis of Section 2 the matrix is **upper-triangular with unit diagonal**: $B_{ii}=1$ for every $i$ and $B_{ij}=0$ whenever $i>j$, so the diagonal is the graph's unique perfect matching.
--
--   The columns are ranked from $n$ (highest) down to $1$, and the rows arrive one at a time in a uniformly random order $\sigma$. Algorithm **EARLY** treats an arriving row $i$ as follows: if column $i$ has already been matched during this run, row $i$ is refused (left unmatched); otherwise row $i$ is matched to the highest-ranked column that is adjacent to it and still unmatched, if there is one. Write
--   $$E(B)=\frac{1}{n!}\sum_{\sigma}\bigl|M_{\mathrm{EARLY}}(B,\sigma)\bigr|$$
--   for the expected size of the matching EARLY produces, the average over all $n!$ arrival orders.
--
--   **Theorem 1.** The performance of EARLY is $n(1-1/e)+o(n)$. Since performance is the minimum of $E(B)$ over the admissible matrices, this means two things:
--
--   1. for every $\varepsilon>0$ there is $N$ such that for every $n\ge N$ and every $n\times n$ upper-triangular matrix $B$ with unit diagonal,
--   $$E(B)\ \ge\ \Bigl(1-\frac1e-\varepsilon\Bigr)n;$$
--   2. for every $\varepsilon>0$ there is $N$ such that for every $n\ge N$ some $n\times n$ upper-triangular matrix $B$ with unit diagonal has
--   $$E(B)\ \le\ \Bigl(1-\frac1e+\varepsilon\Bigr)n.$$
--
--   In the paper the lower bound for EARLY is the step from which the $n(1-1/e)-o(n)$ guarantee for RANKING on every graph with a perfect matching follows (RANKING does at least as well as EARLY on upper-triangular matrices, and the upper-triangular case is the worst case). The upper clause says the constant $1-1/e$ cannot be improved for EARLY.
--
--   **Formalization Note** Indices are zero-based: row and column $i\in\{0,\dots,n-1\}$, with column $n-1$ ranked highest. The matrix is a relation `adj` on `Fin n`, with the two standing hypotheses `∀ i, adj i i` and `∀ i j, adj i j → i ≤ j`. EARLY and $E(B)$ are the published `earlyMatching` and `earlyExpectation`, whose refusal test is evaluated against the matching built so far in the same run. The paper writes $o(n)$; formally each clause is a limit statement with $N$ chosen before the matrix, so the error term is uniform over all admissible matrices of a given size.
--
--   Differences from the source:
--
--   - encoding: rows and columns are numbered 1 to n, column n highest → zero-based indices, column n − 1 highest, and B is a relation on Fin n; reason: a relabelling that changes no instance
--   - reading: "the performance of EARLY is n(1−1/e)+o(n)", with o(n) unquantified → a uniform lower bound (1 − 1/e − ε)n for all large n over every admissible matrix, and an upper bound (1 − 1/e + ε)n attained by some admissible matrix for all large n; reason: performance is the minimum over inputs of the expected size (p. 352), so "is" asserts both that the minimum is at least and at most n(1 − 1/e) up to o(n), and the o(n) must be uniform over the matrices it minimizes over
-- source:
--   Karp, Vazirani, Vazirani, An Optimal Algorithm for On-line Bipartite Matching, STOC 1990, p. 356, Theorem 1; model p. 352 (Section 2, Problem Statement), rows-arrive picture p. 353, standing assumption and EARLY p. 354

import Definitions.Def_KVVMatching_Ranking_Algorithms

namespace KVVMatching.UpperBound.Supplement
open KVVMatching.Ranking

/-- Karp, Vazirani and Vazirani, Theorem 1 (p. 356): the performance of EARLY on
upper-triangular matrices with unit diagonal, rows arriving in uniformly random order,
is `n(1 − 1/e) + o(n)`. The first clause is the uniform lower bound, the second says
the bound is attained up to `εn` by some admissible matrix. -/
theorem theorem_1 :
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ adj : Fin n → Fin n → Prop, (∀ i, adj i i) → (∀ i j, adj i j → i ≤ j) →
        (1 - Real.exp (-1) - ε) * (n : ℝ) ≤ earlyExpectation adj) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ adj : Fin n → Fin n → Prop, (∀ i, adj i i) ∧ (∀ i j, adj i j → i ≤ j) ∧
        earlyExpectation adj ≤ (1 - Real.exp (-1) + ε) * (n : ℝ)) := by sorry

end KVVMatching.UpperBound.Supplement
