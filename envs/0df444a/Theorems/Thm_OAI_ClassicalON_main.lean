-- Prove2me | Theorems.Thm_OAI_ClassicalON_main
-- name    : OAI.ClassicalON.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:26.577186+00:00
-- url     : https://prove2.me/theorems/07598fe4-0f4e-4735-8d92-3ca00150d233
-- statement:
--   The theorem states that the proposition ExponentialDecay holds, a clustering statement for classical O(n) spin models on finite subgraphs of the square lattice ℤ². A lattice graph is a finite set of sites in ℤ×ℤ together with a finite set of directed edges between those sites, each joining a site to its neighbor one step in the positive first or positive second coordinate. A spin is a unit vector in n-dimensional Euclidean space, and a configuration assigns a spin to every vertex. The reference law is the product over vertices of the normalized surface measure on the unit sphere. Given real edge couplings b, the interaction of a configuration is the sum over edges of b(e) times the inner product of the spins at the edge's two endpoints; the partition function is the reference-law integral of exp(interaction), and the correlation of vertices x and y is the integral of ⟨σ_x,σ_y⟩ exp(interaction) divided by the partition function. ExponentialDecay says that for every n ≥ 3 and every β > 0 there exist real constants A and m with m > 0 such that, for every lattice graph G and every choice of couplings with 0 ≤ b(e) ≤ β on all edges, and for all vertices x, y of G, the correlation is nonnegative and at most A·exp(−m·d(x,y)), where d is the Euclidean distance between the sites. The constants A and m depend only on n and β, not on the graph, couplings, or vertices.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ClassicalON.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ClassicalON.lean; bytes 1884..1929
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ClassicalON

namespace OAI

noncomputable section

open MeasureTheory

open scoped BigOperators InnerProductSpace

namespace ClassicalON

theorem main : ExponentialDecay := by
  sorry

end ClassicalON
end
end OAI
