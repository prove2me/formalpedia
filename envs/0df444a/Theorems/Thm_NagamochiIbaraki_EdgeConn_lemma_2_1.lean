-- Prove2me | Theorems.Thm_NagamochiIbaraki_EdgeConn_lemma_2_1
-- name    : NagamochiIbaraki.EdgeConn.lemma_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:04:52.788982+00:00
-- url     : https://prove2.me/theorems/83490c28-d2b2-49f6-ac7e-88749c06dc44
-- title:
--   Lemma 2.1 — successive maximal spanning forests F_i give λ(x, y; G_i) ≥ min{λ(x, y; G), i}
-- statement:
--   Let $G = (V, E)$ be a finite graph with $|V| \ge 2$ and no self-loop, simple or multiple. Let $E_1, E_2, \dots, E_{|E|} \subseteq E$ be edge sets such that, for each $i = 1, 2, \dots, |E|$, the spanning subgraph $F_i = (V, E_i)$ is a maximal spanning forest in $G - (E_1 \cup E_2 \cup \cdots \cup E_{i-1})$ (possibly $E_i = E_{i+1} = \cdots = E_{|E|} = \emptyset$ from some $i$ on). Write $G_i = (V, E_1 \cup E_2 \cup \cdots \cup E_i)$. Then for every $i = 1, 2, \dots, |E|$,
--
--   $$
--   \lambda(x, y; G_i) \;\ge\; \min\{\lambda(x, y; G),\ i\} \qquad \text{for all } x, y \in V, \tag{2.1}
--   $$
--
--   where $\lambda(x, y; H)$ is the local edge-connectivity between $x$ and $y$ in $H$, the minimum number of edges whose removal disconnects $x$ from $y$.
--
--   This is the result, also found independently by Nishizeki and Poljak, that a union of $i$ successively chosen maximal spanning forests preserves all local edge-connectivities up to $i$. It does not refer to any algorithm; Lemma 2.5 shows that FOREST produces such a sequence of forests in one scan.
--
--   **Formalization Note** The sequence is a function $F \colon \mathbb{N} \to 2^E$ of which only the values at $1, \dots, |E|$ matter. Local edge-connectivity takes values in `ℕ∞` and equals $\infty$ at $x = y$, where (2.1) holds trivially; parallel edges count separately in cuts.
-- source:
--   Nagamochi, Ibaraki, A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph, Algorithmica 7 (1992), p. 584, Lemma 2.1 and (2.1)

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_EdgeConn_localEdgeConn

namespace NagamochiIbaraki.EdgeConn

theorem lemma_2_1
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (F : ℕ → Finset E)
    (hF : ∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card E →
      IsMaxSpanningForest ends (Finset.univ \ (Finset.Icc 1 (i - 1)).biUnion F) (F i)) :
    ∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card E → ∀ x y : V,
      min (localEdgeConn ends Finset.univ x y) (i : ℕ∞) ≤
        localEdgeConn ends ((Finset.Icc 1 i).biUnion F) x y := by sorry

end NagamochiIbaraki.EdgeConn
