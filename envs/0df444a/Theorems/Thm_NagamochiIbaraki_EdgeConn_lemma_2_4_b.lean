-- Prove2me | Theorems.Thm_NagamochiIbaraki_EdgeConn_lemma_2_4_b
-- name    : NagamochiIbaraki.EdgeConn.lemma_2_4_b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:03:46.302058+00:00
-- url     : https://prove2.me/theorems/f583d086-79f2-4280-a6b6-c41af1c8e411
-- title:
--   Lemma 2.4(b) — a path in E_j yields paths between the same nodes in every E_i, i < j
-- statement:
--   Let $G = (V, E)$ be a finite multigraph without self-loops and with $|V| \ge 2$, and let $E_1, E_2, \dots, E_{|E|}$ be the classes held by Procedure FOREST at some time instant of any execution on $G$. If nodes $u$ and $v$ are connected by a path $P_j \subseteq E_j$, then for every $i$ with $1 \le i < j$ they are also connected by a path
--
--   $$
--   P_i \subseteq E_i .
--   $$
--
--   So the connected components of the forests $(V, E_1), (V, E_2), \dots$ are nested: each is contained in a component of every earlier forest. This is the property used to prove maximality in Lemma 2.5, and it is used again for node-connectivity in §3 of the paper.
--
--   **Formalization Note** "A path in $E_j$" is reachability in the graph formed by the edges of $E_j$. The instant is any state $\sigma_k$, $k \le K$, of a run, and $j$ ranges up to $|E|$ as in the paper.
-- source:
--   Nagamochi, Ibaraki, A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph, Algorithmica 7 (1992), p. 588, Lemma 2.4(b)

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_EdgeConn_localEdgeConn
import Definitions.Def_NagamochiIbaraki_EdgeConn_Forest

namespace NagamochiIbaraki.EdgeConn

theorem lemma_2_4_b
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsRun ends σ K) :
    ∀ k, k ≤ K → ∀ (i j : ℕ) (u v : V), 1 ≤ i → i < j → j ≤ Fintype.card E →
      (edgeGraph ends (cls (σ k) j)).Reachable u v →
        (edgeGraph ends (cls (σ k) i)).Reachable u v := by sorry

end NagamochiIbaraki.EdgeConn
