-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_directional_transience_implies_ballisticity
-- name    : OAI.DirectionalTransience.directional_transience_implies_ballisticity
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:35.059825+00:00
-- url     : https://prove2.me/theorems/194f4fdd-1414-4fc2-9885-0706bf9acd3b
-- statement:
--   The theorem (admitted, not proved here) states that, for every dimension d ≥ 2 and every Borel probability measure ν on the set of transition rows (a row is a probability vector p over the 2d nearest-neighbour directions ±e_i of ℤ^d, with entries nonnegative and summing to 1), the following holds. Suppose ν is uniformly elliptic, meaning there is κ > 0 with p(e) ≥ κ for every direction e, for ν-almost every row p. Let ℓ be a unit vector in ℝ^d (ℓ·ℓ = 1), and suppose the walk is directionally transient in direction ℓ. Here the environment assigns to each site of ℤ^d an independent ν-distributed row, the walk starts at the origin and at each step moves from its current site x in direction e with probability given by the row at x, and the annealed law averages over the environment and the walk. Directional transience means that, almost surely under this annealed law, the inner product of the walk position X_n with ℓ tends to +∞ as n → ∞. The conclusion is that there exists a vector v ∈ ℝ^d with v·ℓ > 0 such that the walk has asymptotic velocity v, that is, X_n/n → v as n → ∞ almost surely under the annealed law. In other words, directional transience of an i.i.d. uniformly elliptic random walk in random environment in dimension at least two implies ballisticity with a nonzero velocity having positive component along ℓ.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DirectionalBallisticity.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DirectionalBallisticity.lean; bytes 3828..3909
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_DirectionalBallisticity

namespace OAI

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

open scoped ENNReal NNReal Classical Topology BigOperators

theorem directional_transience_implies_ballisticity : MainStatement := by
  sorry

end DirectionalTransience
end OAI
