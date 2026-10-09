-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_main
-- name    : OAI.SidorenkoCounterexample.main
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-07T04:33:21.25389+00:00
-- url     : https://prove2.me/theorems/0ce79ce5-9403-45c0-9a5a-6c2607be713f
-- statement:
--   The theorem states that there exist a positive natural number n and a simple graph host on the vertex set Fin n, with at least one edge (some pair of vertices left, right adjacent), such that homDensity(H, host) < edgeDensity(host)^66. Here H is a fixed bipartite pattern graph on 13 points plus 22 faces, where each face is a specified 3-element subset of the 13 points (for example {0,1,3} and {8,9,12}) and a point is adjacent to a face exactly when it belongs to it; there are no other edges. homCount(F,G) is the number of all vertex maps from F to G sending edges to edges, including non-injective ones, and homDensity(F,G) is that count divided by |V(G)| raised to the power |V(F)|. edgeDensity(G) is 2|E(G)| divided by |V(G)|^2. Since the pattern has 35 vertices and 66 edges, this says the host has homomorphism density below the Sidorenko-type bound edgeDensity^66, so Sidorenko's inequality fails for H. The theorem is admitted in the source, not proved.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SidorenkoCounterexample.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SidorenkoCounterexample.lean; bytes 1459..1725
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SidorenkoCounterexample

namespace OAI

namespace SidorenkoCounterexample

/-- A finite simple host with at least one edge violates Sidorenko's inequality. -/
theorem main : ∃ size : ℕ, 0 < size ∧ ∃ host : SimpleGraph (Fin size),
    (∃ left right, host.Adj left right) ∧ homDensity H host < (edgeDensity host) ^ 66 := by
  sorry

end SidorenkoCounterexample
end OAI
