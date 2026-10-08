-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_finite_bridge_sums
-- name    : OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:05.539463+00:00
-- url     : https://prove2.me/theorems/20b7be08-4668-4f01-99ac-169bee254408
-- statement:
--   The theorem states that, for every integer h ≥ 1, six families of sums over self-avoiding bridge paths in a honeycomb strip are absolutely summable. Vertices of the honeycomb lattice are of two kinds, up(i,j) and down(i,j) with integer i and j, and the layer of a vertex is its second index j; an up vertex (i,j) is adjacent to the down vertices (i,j−1), (i,j) and (i−1,j), and adjacency is symmetric. A bridge path of height h is a list of distinct vertices, consecutive ones adjacent, starting at up(0,0), ending at some down(i,h−1), with every vertex in layers 0 through h−1. Its weight is λ^L, where L is the number of vertices and λ = 1/(2cos(π/8)) is the critical activity, and its first-length weight is L·λ^L. Let bridgeMass(h) be the total weight of all bridge paths. A path is confined if every vertex has horizontal coordinate (i + j/2 for up vertices, i + j/2 + 1/2 for down vertices) of absolute value at most h(log h)², and confinedMass(h) is the total weight of confined paths. The theorem asserts summability over all bridge paths of the weight, of the first-length weight, and of the first-length weight divided by bridgeMass(h), and summability over confined paths of the weight, of the first-length weight, and of the first-length weight divided by confinedMass(h). The proof is admitted in the source, not established here.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HoneycombBridgeFiniteness.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HoneycombBridgeFiniteness.lean; bytes 2261..2320
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness

namespace OAI

namespace PolynomialVacuumBridge.Corridor

theorem finite_bridge_sums : FiniteBridgeSums := by
  sorry

end PolynomialVacuumBridge.Corridor
end OAI
