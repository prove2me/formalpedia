-- Prove2me | Theorems.Thm_NagamochiIbaraki_NodeConn_lemma_2_4_b
-- name    : NagamochiIbaraki.NodeConn.lemma_2_4_b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:08:46.755878+00:00
-- url     : https://prove2.me/theorems/9a26cb64-b837-4e23-bb98-34530546f363
-- title:
--   Lemma 2.4(b) — at any instant of FOREST, a u–v path in E*_j gives u–v paths in every E*_i with i < j
-- statement:
--   Let $G = (V, E)$ be a graph with $|V| \ge 2$ and no self-loop, and consider any run of Procedure FOREST on $G$. Fix a time instant and let $E^*_1, E^*_2, \dots$ be the classes at that instant. For indices $1 \le i < j \le |E|$ and nodes $u, v$:
--
--   $$
--   u \text{ and } v \text{ are connected by a path in } E^*_j \ \Longrightarrow\ u \text{ and } v \text{ are connected by a path in } E^*_i .
--   $$
--
--   Connectivity is thus monotone across the classes: a later forest never joins two nodes that an earlier forest leaves apart. The proof of Lemma 3.2 uses it to produce the paths $P_t$, $P'_t$ to which Lemma 3.1 is applied.
--
--   **Formalization Note** "Connected by a path in $E^*_j$" is reachability in the spanning subgraph $(V, E^*_j)$; a path exists exactly when a walk does.
-- source:
--   Nagamochi, Ibaraki, A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph, Algorithmica 7 (1992), p. 588, Lemma 2.4(b)

import Mathlib
import Definitions.Def_NagamochiIbaraki_NodeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_NodeConn_Forest

namespace NagamochiIbaraki.NodeConn

theorem lemma_2_4_b
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsRun ends σ K) :
    ∀ k, k ≤ K → ∀ (i j : ℕ) (u v : V), 1 ≤ i → i < j → j ≤ Fintype.card E →
      (edgeGraph ends (cls (σ k) j)).Reachable u v →
        (edgeGraph ends (cls (σ k) i)).Reachable u v := by sorry

end NagamochiIbaraki.NodeConn
