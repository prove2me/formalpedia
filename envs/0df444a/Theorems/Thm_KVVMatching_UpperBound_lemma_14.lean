-- Prove2me | Theorems.Thm_KVVMatching_UpperBound_lemma_14
-- name    : KVVMatching.UpperBound.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:14:26.133844+00:00
-- url     : https://prove2.me/theorems/1a110534-f1ce-4106-b524-8fd825e60bbe
-- title:
--   Lemma 14 — universal upper bound from RANDOM on the triangular instance
-- statement:
--   For every randomized on-line matching algorithm $A$ on $n$ rows and $n$ columns, some graph $G$ with a perfect matching satisfies
--
--   $$\mathbb E_A[|M(G)|]\le V_{T_n}(n,\varnothing).$$
--
--   Thus the worst-case performance of any algorithm is at most RANDOM's expected matching size on the complete upper-triangular graph. The hard graph may depend on the algorithm, as required by the order of the quantifiers.
--
--   **Formalization Note** The statement ranges over all randomized rules, including non-greedy ones. A perfect matching is witnessed by a bijection between boys and girls whose edges lie in $G$.
-- source:
--   Karp, Vazirani, Vazirani, An Optimal Algorithm for On-line Bipartite Matching, STOC 1990, p. 357, Lemma 14

import Mathlib
import Definitions.Def_KVVMatching_UpperBound_RandomValue
import Definitions.Def_KVVMatching_UpperBound_Triangular
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPerfectMatchingBij

namespace KVVMatching.UpperBound

/-- Karp, Vazirani and Vazirani, Lemma 14 (p. 357). -/
theorem lemma_14 (n : ℕ) (A : RandomAlg n) :
    ∃ G : Graph n,
      (∃ σ : Fin n ≃ Fin n,
        DiscreteConvex.IntegralConvexityB.IsPerfectMatchingBij G σ) ∧
      expectedSize G A ≤ randomValue (upperTriangular n) := by sorry

end KVVMatching.UpperBound
