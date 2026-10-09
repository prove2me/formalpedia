-- Prove2me | Theorems.Thm_LinearPathTuran_Exact_theorem_1_1
-- name    : LinearPathTuran.Exact.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:39.360036+00:00
-- url     : https://prove2.me/theorems/7d15897a-8fa6-42df-a26b-55394a76fb00
-- title:
--   Theorem 1.1 (Erdős) — for large n, no t+1 pairwise disjoint k-sets implies |F| ≤ C(n,k) − C(n−t,k), with the star family unique
-- statement:
--   **Erdős' matching theorem for large $n$.** Let $k,t$ be positive integers. There is $n(k,t)$ such that for every $n>n(k,t)$: if $\mathcal F\subseteq\binom{[n]}{k}$ contains no $t+1$ pairwise disjoint members, then
--   $$|\mathcal F|\le\binom{n}{k}-\binom{n-t}{k},$$
--   and equality holds only for the family of all $k$-subsets of $[n]$ meeting some fixed set $S$ of $t$ elements.
--
--   In the paper it bounds, in equation (5), the $(k-2)$-uniform link families that arise near the exceptional set.
--
--   **Formalization Note** $n(k,t)$ is an existential threshold chosen after $k,t$. The equality clause is an equivalence: a family under the hypotheses has exactly $\binom nk-\binom{n-t}k$ members iff it is the star family of some $t$-set. The subtraction $\binom nk-\binom{n-t}k$ is exact in $\mathbb N$. The theorem is cited from Erdős (1965).
-- source:
--   Füredi, Jiang and Seiver, Exact solution of the hypergraph Turán problem for k-uniform linear paths, arXiv:1108.1247v1, p. 2, Theorem 1.1 (cited from Erdős, A problem on independent r-tuples, Ann. Univ. Sci. Budapest. 8 (1965))

import Mathlib
import Definitions.Def_LinearPathTuran_Exact_Setting

namespace LinearPathTuran.Exact

open Finset

/-- Theorem 1.1 (Erdős 1965), p. 2: for large `n`, a `k`-uniform family on `[n]` with no `t + 1`
pairwise disjoint members has at most `C(n, k) - C(n - t, k)` members, with equality only for the
family of all `k`-sets meeting a fixed `t`-set. -/
theorem theorem_1_1 (k t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    ∃ n₀ : ℕ, ∀ n > n₀, ∀ 𝓕 : Finset (Finset (Fin n)),
      𝓕 ⊆ (univ : Finset (Fin n)).powersetCard k →
      (¬ ∃ 𝓜 ⊆ 𝓕, #𝓜 = t + 1 ∧ (𝓜 : Set (Finset (Fin n))).PairwiseDisjoint id) →
      #𝓕 ≤ n.choose k - (n - t).choose k ∧
      (#𝓕 = n.choose k - (n - t).choose k ↔
        ∃ S : Finset (Fin n), #S = t ∧ 𝓕 = starFamily n k S) := by sorry

end LinearPathTuran.Exact
