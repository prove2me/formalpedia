-- Prove2me | Theorems.Thm_LubyMIS_Derandomized_algorithmD_rounds
-- name    : LubyMIS.Derandomized.algorithmD_rounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T23:01:06.399984+00:00
-- url     : https://prove2.me/theorems/117f9efd-e5b6-4185-b871-108f3ffa8039
-- title:
--   Algorithm D stops within log(n²)/log(18/17) + 16 ≤ 25·log n + 16 rounds with a maximal independent set
-- statement:
--   Let $G$ be a graph on the vertices $\{0, \dots, n-1\}$ and let $q$ be a prime with $n \le q \le 2n$. Every run of Algorithm D terminates: there is a $k$ such that the vertex set $V'$ of the current graph is nonempty before each of the first $k$ executions of the loop body and empty after the $k$-th, so the loop body is executed exactly $k$ times. Moreover
--   $$k \ \le\ \frac{\log(n^2)}{\log(18/17)} + 16 \ \le\ 25 \cdot \log_2 n + 16,$$
--   and the output set $I$ is a maximal independent set of $G$.
--
--   This is the deterministic guarantee of Algorithm D: a maximal independent set is found in $O(\log n)$ parallel rounds without random bits, for every choice of maximizing vertex in Case 1 and every choice of maximizing sample point in Case 2.
--
--   **Formalization Note** The ratio $\log(n^2)/\log(18/17)$ does not depend on the base of the logarithm; $25 \log n$ is base 2, following the paper's convention that all logarithms are base 2. The statement holds for every run, that is, for every tie-break among vertices of maximum degree and every maximizing sample point. The P-RAM processor count and running time are not part of the statement. For $n = 0$ no prime $q \le 0$ exists and the statement is vacuous; for $n = 1$ the bound is $16$.
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, p. 1047, §4.4, display on Algorithm D; p. 1039, §3.1 ("I is a maximal independent set in G at the termination of the algorithm")

import Mathlib
import Definitions.Def_LubyMIS_Derandomized_Basic
import Definitions.Def_LubyMIS_Derandomized_AlgorithmD

namespace LubyMIS.Derandomized

/-- Algorithm D (Luby 1986, §4.4, p. 1047, with §3.1, p. 1039): for every graph `G` on `n` vertices
and every prime `n ≤ q ≤ 2n`, every run of Algorithm D stops after `k` executions of the loop body
with `k ≤ log(n²)/log(18/17) + 16 ≤ 25·log₂ n + 16`, and the set `I` it outputs is a maximal
independent set of `G`. -/
theorem algorithmD_rounds (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q : ℕ)
    (hq : q.Prime) (hnq : n ≤ q) (hq2 : q ≤ 2 * n) (s : ℕ → Finset (Fin n) × Finset (Fin n))
    (hs : IsRun G q s) :
    ∃ k : ℕ, (s k).2 = ∅ ∧ (∀ j < k, (s j).2.Nonempty) ∧
      (k : ℝ) ≤ Real.log ((n : ℝ) ^ 2) / Real.log (18 / 17) + 16 ∧
      (k : ℝ) ≤ 25 * Real.logb 2 (n : ℝ) + 16 ∧
      Maximal G.IsIndepSet ((s k).1 : Set (Fin n)) := by sorry

end LubyMIS.Derandomized
