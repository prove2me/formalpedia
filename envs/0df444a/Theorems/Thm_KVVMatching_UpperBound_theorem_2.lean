-- Prove2me | Theorems.Thm_KVVMatching_UpperBound_theorem_2
-- name    : KVVMatching.UpperBound.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:15:45.580191+00:00
-- url     : https://prove2.me/theorems/212afd75-eba3-44eb-9fcc-6fbcd5a3f8b7
-- title:
--   Theorem 2 — no on-line algorithm exceeds the asymptotic bound
-- statement:
--   For every $\varepsilon>0$, there is an $N$ such that for every $n\ge N$ and every randomized on-line matching algorithm $A$ on $n$ boys and $n$ girls, some graph $G$ containing a perfect matching satisfies
--
--   $$\mathbb E_A[|M(G)|]\le (1-e^{-1}+\varepsilon)n.$$
--
--   Hence the performance of every algorithm is at most $n(1-1/e)+o(n)$ in the paper's sense. The threshold $N$ is independent of $A$; the hard graph is chosen after $A$.
--
--   **Formalization Note** The paper writes $o(n)$; the quantified inequality is its uniform upper-bound form. The fixed reverse order of columns represents any preselected order after relabeling the girls.
-- source:
--   Karp, Vazirani, Vazirani, An Optimal Algorithm for On-line Bipartite Matching, STOC 1990, p. 357, Theorem 2

import Mathlib
import Definitions.Def_KVVMatching_UpperBound_RandomValue
import Definitions.Def_KVVMatching_UpperBound_Triangular
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPerfectMatchingBij

namespace KVVMatching.UpperBound

/-- Karp, Vazirani and Vazirani, Theorem 2 (p. 357), with uniform `o(n)`. -/
theorem theorem_2 :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ A : RandomAlg n, ∃ G : Graph n,
        (∃ σ : Fin n ≃ Fin n,
          DiscreteConvex.IntegralConvexityB.IsPerfectMatchingBij G σ) ∧
        expectedSize G A ≤ (1 - Real.exp (-1) + ε) * (n : ℝ) := by sorry

end KVVMatching.UpperBound
