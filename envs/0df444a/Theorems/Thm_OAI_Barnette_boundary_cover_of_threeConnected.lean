-- Prove2me | Theorems.Thm_OAI_Barnette_boundary_cover_of_threeConnected
-- name    : OAI.Barnette.boundary_cover_of_threeConnected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:04:40.121094+00:00
-- url     : https://prove2.me/theorems/b82a288e-751b-45b7-a9aa-8d865afdd615
-- title:
--   In a 3-connected graph, a vertex set attached to the rest only through at most two of its vertices consists of those vertices
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$. Call $G$ *three-vertex-connected* if $|V|\ge4$ and deleting any set of at most two vertices leaves a connected graph: for every $S\subseteq V$ with $|S|\le2$, the subgraph $G-S$ induced on $V\setminus S$ is connected.
--
--   **Theorem.** Let $G$ be three-vertex-connected, and let $A,S\subseteq V$ satisfy $|S|\le2$, $S\subseteq A$ and $A\ne V$. Assume that every vertex of $A$ having a neighbour outside $A$ belongs to $S$:
--
--   $$\forall v\in A,\ \forall w\in V\setminus A:\qquad vw\in E(G)\ \Longrightarrow\ v\in S.$$
--
--   Then $A\subseteq S$, that is, $A=S$.
--
--   In words, a vertex set that is attached to the rest of a 3-connected graph only through at most two of its own vertices consists of those vertices alone; otherwise these at most two vertices would separate a vertex of $A\setminus S$ from the vertices outside $A$. This is the form in which three-vertex-connectivity is used to exclude small separations.
--
--   **Formalization Note** $A$ and $S$ are `Finset`s, the hypothesis $A\ne V$ is stated as `∃ w, w ∉ A`, and $G-S$ is `G.induce {v | v ∉ S}`. The lower bound $|V|\ge4$ contained in `ThreeVertexConnected` is not needed for this statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Network.lean#L239-L261

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network

open OAI OAI.Barnette
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
theorem OAI.Barnette.boundary_cover_of_threeConnected (h : ThreeVertexConnected G)
    (A S : Finset V) (hS : S.card ≤ 2) (hSA : S ⊆ A)
    (hout : ∃ w, w ∉ A)
    (hboundary : ∀ v ∈ A, ∀ w, w ∉ A → G.Adj v w → v ∈ S) : A ⊆ S := by sorry
