-- Prove2me | Theorems.Thm_JohnsonApprox_MaxSatGreedy_greedy_maxsat_ratio
-- name    : JohnsonApprox.MaxSatGreedy.greedy_maxsat_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:24:25.670921+00:00
-- url     : https://prove2.me/theorems/99413013-75d9-4d90-8261-340475c06c87
-- title:
--   Theorem 2 — R[B1, MS(k)](n) ≤ (k + 1)/k for all k ≥ 1, with equality for all sufficiently large n
-- statement:
--   Johnson (1974), Theorem 2: "For all $k \ge 1$ and $n > 0$, $R[B1, MS(k)](n) \le (k+1)/k$, with equality for all sufficiently large $n$."
--
--   Here $MS(k)$ is MAXIMUM SATISFIABILITY restricted to sets of clauses each with at least $k$ distinct literals, $S^*$ is the largest number of clauses of $S$ satisfiable by one truth assignment, and B1 is the greedy algorithm that repeatedly makes true a literal occurring in the most remaining clauses. In size-free form the theorem says: for every integer $k \ge 1$,
--
--   1. for every input $S$ of $MS(k)$ and every set $X$ of clauses choosable by B1 on $S$,
--   $$k \cdot S^* \;\le\; (k+1)\cdot |X|;$$
--   2. there are an input $S$ of $MS(k)$ and a set $X$ choosable by B1 on $S$ with $|X| > 0$ and
--   $$k \cdot S^* = (k+1)\cdot |X|.$$
--
--   The first part is the upper bound; the second shows that the ratio $(k+1)/k$ is attained, so it is the exact worst-case ratio of B1 on $MS(k)$ for every $k$.
--
--   **Formalization Note** The paper's $R[A,P](n)$ is a maximum of the ratio $S^*/B1(S)$ over inputs of size at most $n$, where the size is "the number of symbols required to describe $u$ in some standard notation" and is not pinned down. Since $B1(S)$ is the minimum over choosable outputs and $R$ is a nondecreasing maximum over finitely many inputs, "$R \le c$ for all $n$" is equivalent to part 1, and "equality for all sufficiently large $n$" (given part 1) is equivalent to part 2. Ratios are written multiplicatively in $\mathbb{N}$ so that no division by zero arises; $|X| > 0$ in part 2 excludes the degenerate empty input. Choosability ranges over every tie-break of Step 3.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 262, Theorem 2

import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatGreedy_B1

namespace JohnsonApprox.MaxSatGreedy

theorem greedy_maxsat_ratio (k : ℕ) (hk : 1 ≤ k) :
    (∀ (S : Finset Shared.Clause), Shared.InMS k S → ∀ X : Finset Shared.Clause, Choosable S X →
        k * Shared.opt S ≤ (k + 1) * X.card) ∧
      (∃ (S : Finset Shared.Clause), Shared.InMS k S ∧ ∃ X : Finset Shared.Clause, Choosable S X ∧
        0 < X.card ∧ k * Shared.opt S = (k + 1) * X.card) := by sorry

end JohnsonApprox.MaxSatGreedy
