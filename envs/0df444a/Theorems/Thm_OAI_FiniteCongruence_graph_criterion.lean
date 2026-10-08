-- Prove2me | Theorems.Thm_OAI_FiniteCongruence_graph_criterion
-- name    : OAI.FiniteCongruence.graph_criterion
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:40.449272+00:00
-- url     : https://prove2.me/theorems/3a6b2c5a-c9e5-4198-ae45-0179bf28ead4
-- statement:
--   The theorem states that, for any finite type Lat carrying a lattice structure with a least element ⊥, Lat is Representable if and only if it HasGraphWitness. Representable means that there is a positive size n and an algebra on Fin n (a finite list of operations, each of some finite arity, acting on the carrier) such that Lat is order-isomorphic to the poset of congruences of that algebra, where a congruence is an equivalence relation compatible with every operation: if corresponding arguments are related coordinatewise, the outputs are related; congruences are ordered by the inherited order on equivalence relations. HasGraphWitness means that there is a positive size n and a Lat-valued coloring color of ordered pairs from Fin n satisfying five conditions: color is symmetric; color(a,b)=⊥ exactly when a=b; color(a,b) ≤ color(a,m) ⊔ color(m,b) for all a, b, m; whenever lower ≰ upper in Lat, some pair has color ≤ lower but not ≤ upper; and for every nonempty finite set of seed pairs, any pair whose color is at most the join of the seed colors is connected to the seeds. Connected is the equivalence closure of the relation Marked, where a,b are Marked if some self-map p of the vertices satisfies color(p x,p y) ≤ color(x,y) for all x,y and sends some seed pair (s,t) to (a,b).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/FiniteCongruenceGraph.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FiniteCongruenceGraph.lean; bytes 2595..2898
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Hom.Basic
import Definitions.Def_FiniteCongruenceGraph

namespace OAI

namespace FiniteCongruence

/-- A finite lattice is representable as the full congruence lattice of a nonempty finite
algebra exactly when it has a finite nonempty colored-graph witness. -/
theorem graph_criterion (Lat : Type) [Fintype Lat] [Lattice Lat] [OrderBot Lat] :
    Representable Lat ↔ HasGraphWitness Lat := by
  sorry

end FiniteCongruence
end OAI
