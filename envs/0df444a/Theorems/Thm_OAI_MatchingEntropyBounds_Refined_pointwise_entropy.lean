-- Prove2me | Theorems.Thm_OAI_MatchingEntropyBounds_Refined_pointwise_entropy
-- name    : OAI.MatchingEntropyBounds.Refined.pointwise_entropy
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:54.92598+00:00
-- url     : https://prove2.me/theorems/78d05e3b-20b8-4561-a54a-a4a3e6f81377
-- statement:
--   The theorem is stated but admitted (its proof is left as sorry). A loopless graph is given by a finite vertex type V and finite edge type E, with each edge e having distinct endpoints left(e) and right(e). A perfect matching is a set M of edges such that every vertex lies on exactly one edge of M, and the matching polytope is the convex hull in R^E of the 0/1 indicator vectors of perfect matchings. For a point y in R^E, a feasible law is a probability distribution p on the perfect matchings whose mean, the sum over matchings M of p(M) times the indicator of M, equals y, and maxMatchingEntropy(G,y) is the supremum of the Shannon entropy sum of -t log t over the weights of p, taken over all feasible laws. The entropy of a real vector is the sum of negMulLog over its coordinates, and complementEntropy(x) is the entropy of the vector with coordinates 1 - x_e. The theorem states that, for a loopless graph G, a positive integer m with |V| = 2m, at least one perfect matching, and any x in the matching polytope, entropy(x) - (2 - 2/m) * complementEntropy(x) is at most maxMatchingEntropy(G,x), which in turn is at most entropy(x).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MatchingEntropyBounds.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MatchingEntropyBounds.lean; bytes 2081..2415
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_MatchingEntropyBounds

namespace OAI

noncomputable section

open scoped BigOperators Topology

open Filter

universe uV uE uIndex uι

namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE}
  [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

open Module Matrix

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

open LooplessGraph

theorem Refined.pointwise_entropy (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) (hPM : Nonempty G.Matching)
    (x : E → ℝ) (hx : x ∈ G.polytope) :
    entropy x - (2 - 2 / (m : ℝ)) * complementEntropy x ≤ maxMatchingEntropy G x ∧
      maxMatchingEntropy G x ≤ entropy x := by
  sorry

end MatchingEntropyBounds
end
end OAI
