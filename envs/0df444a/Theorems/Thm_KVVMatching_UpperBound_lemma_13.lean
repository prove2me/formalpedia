-- Prove2me | Theorems.Thm_KVVMatching_UpperBound_lemma_13
-- name    : KVVMatching.UpperBound.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:13:55.282695+00:00
-- url     : https://prove2.me/theorems/c5c25f5d-8c3a-4b4b-a80d-a9120c3b39e7
-- title:
--   Lemma 13 — greedy algorithms on permuted triangular instances
-- statement:
--   Let $T_n$ be the complete upper-triangular bipartite graph with $n$ rows and $n$ columns. For every deterministic greedy on-line algorithm $a$, the average matching size over uniform row permutations $\pi$ equals the expected matching size of RANDOM on $T_n$:
--
--   $$\frac{1}{n!}\sum_{\pi}|M_a(T_\pi)|=V_{T_n}(n,\varnothing).$$
--
--   This identifies the value of every greedy deterministic rule against the paper's uniform hard-input distribution.
--
--   **Formalization Note** The row permutation sends the old row $i$ to $\pi(i)$; reversing this convention leaves the uniform average unchanged. The equation also holds when $n=0$.
-- source:
--   Karp, Vazirani, Vazirani, An Optimal Algorithm for On-line Bipartite Matching, STOC 1990, p. 357, Lemma 13

import Mathlib
import Definitions.Def_KVVMatching_UpperBound_RandomValue
import Definitions.Def_KVVMatching_UpperBound_Triangular

namespace KVVMatching.UpperBound

/-- Karp, Vazirani and Vazirani, Lemma 13 (p. 357). -/
theorem lemma_13 (n : ℕ) (a : DetAlg n) (ha : IsGreedy a) :
    (1 / (n.factorial : ℝ)) *
      (∑ π : Equiv.Perm (Fin n),
        (matchingSize (permutedTriangular π) a : ℝ)) =
      randomValue (upperTriangular n) := by sorry

end KVVMatching.UpperBound
