-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_entropy_main
-- name    : OAI.MatchingEntropy.entropy_main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:55.04602+00:00
-- url     : https://prove2.me/theorems/e6852eb2-f9b2-4015-806a-58acab4b5f4a
-- statement:
--   The theorem states that, for a loopless graph G on a finite vertex set V with finite edge set E (each edge e has distinct endpoints left(e) and right(e)), a positive integer m with |V| = 2m, at least one perfect matching of G (a set of edges such that every vertex lies on exactly one chosen edge), and any edge-weight vector y: E → ℝ lying in the matching polytope of G (the convex hull in ℝ^E of the 0/1 indicator vectors of the perfect matchings), the following bound holds. Let marginalEntropy(y) be H(y) = Σ_e −y_e log y_e, using Mathlib's negMulLog, and let maxMatchingEntropy(G,y) be the supremum of the entropy Σ_M −p_M log p_M over all probability laws p on the perfect matchings whose mean Σ_M p_M·1[e ∈ M] equals y_e for every edge e. Then H(y) − maxMatchingEntropy(G,y) ≤ 8m(1 − exp(−H(y)/m)). This is stated as an admitted theorem (its proof is left as sorry).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MatchingEntropy.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MatchingEntropy.lean; bytes 1677..2071
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_MatchingEntropy

namespace OAI

noncomputable section

open scoped BigOperators

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Main entropy comparison, for every marginal in the actual matching polytope. -/
theorem entropy_main (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m)
    (hPM : Nonempty G.Matching) (y : E → ℝ) (hy : y ∈ G.polytope) :
    marginalEntropy y - maxMatchingEntropy G y ≤
      8 * (m : ℝ) * (1 - Real.exp (-marginalEntropy y / (m : ℝ))) := by
  sorry

end MatchingEntropy
end
end OAI
