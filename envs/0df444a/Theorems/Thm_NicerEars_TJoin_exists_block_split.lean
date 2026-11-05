-- Prove2me | Theorems.Thm_NicerEars_TJoin_exists_block_split
-- name    : NicerEars.TJoin.exists_block_split
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T11:24:38.437856+00:00
-- url     : https://prove2.me/theorems/7a098921-288a-4e93-bbd8-e61507d8ef15
-- title:
--   A connected graph that is not 2-vertex-connected splits at a vertex into two smaller connected graphs
-- statement:
--   Let $G$ be a connected finite multigraph (parallel edges allowed, no loops) with $|V(G)|\ge 3$ which is **not** 2-vertex-connected (in the sense of the mission's setting: 2-edge-connected and without a vertex whose deletion disconnects the remaining graph). Then there are a vertex $v$, vertex sets $V_1,V_2\subseteq V(G)$ and edge sets $E_1,E_2\subseteq E(G)$ such that
--
--   - $V_1\cup V_2=V(G)$, $V_1\cap V_2=\{v\}$, $V_1\ne V(G)$, $V_2\ne V(G)$;
--   - $E_1\cup E_2=E(G)$ and $E_1\cap E_2=\emptyset$;
--   - every edge of $E_i$ has both endpoints in $V_i$, and $G_i=(V_i,E_i)$ is connected ($i=1,2$).
--
--   Thus $G$ is the union of two connected graphs, each with fewer vertices than $G$, meeting in exactly one vertex — exactly the situation of Proposition 4. This is the standard fact behind the remark on p. 5 of Sebő–Vygen that one may treat the blocks (maximal 2-vertex-connected subgraphs) separately. (If $G$ has a bridge but no cut vertex, $|V(G)|\ge3$ forces an endpoint of the bridge to be a cut vertex; at a cut vertex $v$ take $V_1=C\cup\{v\}$ for one component $C$ of $G-v$.)
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 5 (remark preceding Proposition 4: 'we can consider the blocks (i.e., the maximal 2-vertex-connected subgraphs) separately'); standard block decomposition of graphs

import Mathlib
import Definitions.Def_NicerEars_TJoin_Setting

namespace NicerEars.TJoin

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Blocks (Sebő–Vygen, p. 5, remark before Proposition 4): a connected graph `G` with at least
three vertices that is not 2-vertex-connected is the union of two connected graphs
`G₁ = (V₁, E₁)` and `G₂ = (V₂, E₂)` sharing exactly one vertex `v`, with disjoint edge sets, and
each having fewer vertices than `G`. -/
theorem exists_block_split (G : Graph V E) (hG : G.IsConnected) (hnot : ¬ G.IsTwoVertexConnected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (v : V) (V₁ V₂ : Finset V) (E₁ E₂ : Finset E),
      V₁ ∪ V₂ = univ ∧ V₁ ∩ V₂ = {v} ∧ E₁ ∪ E₂ = univ ∧ Disjoint E₁ E₂ ∧ V₁ ≠ univ ∧ V₂ ≠ univ ∧
      ∃ (h₁ : ∀ e ∈ E₁, ∀ u ∈ G.ends e, u ∈ V₁) (h₂ : ∀ e ∈ E₂, ∀ u ∈ G.ends e, u ∈ V₂),
        (G.sub V₁ E₁ h₁).IsConnected ∧ (G.sub V₂ E₂ h₂).IsConnected := by sorry

end NicerEars.TJoin
