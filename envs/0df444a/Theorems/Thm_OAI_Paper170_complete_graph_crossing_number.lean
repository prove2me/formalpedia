-- Prove2me | Theorems.Thm_OAI_Paper170_complete_graph_crossing_number
-- name    : OAI.Paper170.complete_graph_crossing_number
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:00.035915+00:00
-- url     : https://prove2.me/theorems/cf975d81-78e8-45ca-a682-cc5e87f6f173
-- statement:
--   The theorem states that for every natural number n ≥ 3, the ordinary crossing number of the complete graph K_n equals hill(n). Here K_n is the simple loopless graph on vertices Fin n whose edges are the pairs i<j. An admissible drawing places the vertices at distinct points of the plane ℝ×ℝ and draws each edge as an injective continuous path between its endpoints whose interior avoids all vertices. Further, the set of points lying on the interiors of two distinct edges must be finite, each such common point must be a proper crossing (there is a local homeomorphic chart sending the point to the origin, the first edge's interior to the horizontal axis and the second's to the vertical axis), and no point lies on the interiors of three distinct edges. The crossing count of a drawing is the number of such crossing points, and the ordinary crossing number is the infimum (least value) of this count over all admissible drawings. The quantity hill(n) is defined with natural-number floor division as ⌊⌊n/2⌋·⌊(n−1)/2⌋·⌊(n−2)/2⌋·⌊(n−3)/2⌋ / 4⌋. The statement is admitted without proof in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CompleteCrossing.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CompleteCrossing.lean; bytes 3366..3527
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.Path
import Definitions.Def_CompleteCrossing

namespace OAI

noncomputable section

namespace Paper170

variable {Vertex Edge : Type}

variable {graph : Graph Vertex Edge}

theorem complete_graph_crossing_number (order : ℕ) (at_least_three : 3 ≤ order) :
    ordinaryCrossingNumber (completeGraph order) = hill order := by
  sorry

end Paper170
end
end OAI
