-- Prove2me | Theorems.Thm_NonmonotoneSubmod_QueryLB_unbalanced_count_le
-- name    : NonmonotoneSubmod.QueryLB.unbalanced_count_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:16:19.804976+00:00
-- url     : https://prove2.me/theorems/a5cc0e84-9dc0-4174-91ca-84f9bf2caa6d
-- title:
--   §4.2 — a fixed query is unbalanced with probability at most $2e^{-\epsilon^2 n/4}$
-- statement:
--   Let $n$ be even, $1 \le m$, $2m \le n$, and $\epsilon = m/n$. Let $C$ be a uniformly random subset of $[n]$ of size $n/2$ and $D = [n]\setminus C$. For every fixed $Q \subseteq [n]$,
--
--   $$
--   \Pr_C\Bigl[\bigl||Q \cap C| - |Q \cap D|\bigr| > \epsilon n\Bigr] \le 2e^{-\epsilon^2 n/4}.
--   $$
--
--   Equivalently, at most $2e^{-\epsilon^2 n/4}\binom{n}{n/2}$ of the $\binom{n}{n/2}$ half-size subsets $C$ make $Q$ unbalanced. With a union bound over the queries, this shows that an algorithm with few queries sees only balanced sets for most partitions.
--
--   **Formalization Note** The probability over the uniform random partition is written as a count of `n/2`-subsets of `Fin n`. The paper derives the bound from the Chernoff bound for independent variables (Theorem 1.2); since $|Q\cap C|$ is hypergeometric rather than a sum of independent terms, that citation does not apply literally, but the stated bound is true (Hoeffding's inequality for sampling without replacement).
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1150, §4.2, proof of Theorem 4.5, first paragraph ("For any query Q, the probability that Q is unbalanced is at most 2e^{−ϵ²n/4} by Theorem 1.2")

import Mathlib
import Definitions.Def_NonmonotoneSubmod_QueryLB_HardInstance

namespace NonmonotoneSubmod.QueryLB

/-- §4.2, proof of Theorem 4.5 (p. 1150, first paragraph): for a uniformly random
`C ⊆ [n]` with `|C| = n/2` and any fixed query `Q`, the probability that `Q` is unbalanced
(`||Q ∩ C| − |Q ∩ D|| > ϵn`) is at most `2e^{−ϵ²n/4}`; stated as a count of the `n/2`-subsets. -/
theorem unbalanced_count_le (n m : ℕ) (hn : Even n) (hm : 1 ≤ m) (hmn : 2 * m ≤ n)
    (Q : Finset (Fin n)) :
    (((Finset.univ.powersetCard (n / 2)).filter (fun C => ¬ Balanced n m C Q)).card : ℝ) ≤
      2 * Real.exp (-(((m : ℝ) / n) ^ 2 * n / 4)) * (n.choose (n / 2) : ℝ) := by sorry

end NonmonotoneSubmod.QueryLB
