-- Prove2me | Theorems.Thm_OAI_Problem315_switch_connectivity
-- name    : OAI.Problem315.switch_connectivity
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:07.575809+00:00
-- url     : https://prove2.me/theorems/0df629e2-7c26-431b-9ed8-7853266f4730
-- statement:
--   The theorem states that, for every number of vertices n ≥ 4 and every degree assignment d on the vertices {0,…,n−1} with each d(v) ≤ n−1 that is graphical, meaning at least one simple graph on these n labelled vertices has degree exactly d(v) at every vertex v, any two simple graphs G and H realizing d are connected by a finite sequence of switch steps (the reflexive-transitive closure of the switch relation, so zero steps are allowed). A switch step from G to H means there is a proposal consisting of a 4-element vertex set S and two distinct perfect matchings M and N on S, where each matching is a graph in which every vertex of S has exactly one neighbour and vertices outside S have none, such that all edges of M are present in G, no edge of N is present in G, and H is obtained from G by deleting the edges of M and adding the edges of N. Since such a switch preserves every vertex degree, the statement says the space of graphs with the prescribed degree sequence is connected under these four-vertex switches. The theorem is admitted in the source with sorry.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SwitchChain.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SwitchChain.lean; bytes 5467..5675
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SwitchChain

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem315

theorem switch_connectivity :
    ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) → Graphical n d → ∀ G H : GraphState n d, Relation.ReflTransGen (SwitchStep n d) G H := by
  sorry

end Problem315
end
end OAI
