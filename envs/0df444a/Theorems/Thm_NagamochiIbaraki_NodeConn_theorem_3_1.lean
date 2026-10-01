-- Prove2me | Theorems.Thm_NagamochiIbaraki_NodeConn_theorem_3_1
-- name    : NagamochiIbaraki.NodeConn.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:11:24.674992+00:00
-- url     : https://prove2.me/theorems/b1f97168-3daa-4d5e-9398-319c63142c80
-- title:
--   Theorem 3.1 — FOREST's G_i = (V, E_1 ∪ ⋯ ∪ E_i) satisfies κ(x, y; G_i) ≥ min{κ(x, y; G), i} in a simple graph
-- statement:
--   Let $G = (V, E)$ be a simple graph with $|V| \ge 2$, and let $E_1, E_2, \dots, E_{|E|}$ be the edge classes obtained by Procedure FOREST upon completion (for any choice of ties at lines 5 and 6). For $1 \le i \le |E|$ let $G_i = (V, E_1 \cup E_2 \cup \dots \cup E_i)$. Then
--
--   $$
--   \kappa(x, y; G_i) \ \ge\ \min\{\kappa(x, y; G),\ i\} \qquad \text{for any } x, y \in V,
--   $$
--
--   where $\kappa(x, y; H)$ is the local node-connectivity in $H$, equal to $|V| - 1$ when $x$ and $y$ are adjacent in $H$.
--
--   In particular, if $G$ is $k$-node-connected then so is the spanning subgraph $G_k$, which has at most $k|V| - k(k+1)/2$ edges; this makes FOREST a linear-time preprocessing step for node-connectivity algorithms.
--
--   **Formalization Note** $\kappa$ takes values in $\mathbb N_\infty$ and is $\top$ for $x = y$, where the inequality holds trivially. $E_i$ is the set of edges of class $i$ in the final state of a completed run of the nondeterministic step relation encoding FOREST, so the theorem holds for every tie-breaking. The running time $O(|V| + |E|)$ of FOREST is not part of this statement.
-- source:
--   Nagamochi, Ibaraki, A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph, Algorithmica 7 (1992), pp. 589–590, Theorem 3.1, display (3.1)

import Mathlib
import Definitions.Def_NagamochiIbaraki_NodeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_NodeConn_localNodeConn
import Definitions.Def_NagamochiIbaraki_NodeConn_Forest

namespace NagamochiIbaraki.NodeConn

theorem theorem_3_1
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (hsimple : Function.Injective ends)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsCompletedRun ends σ K) :
    ∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card E → ∀ x y : V,
      min (localNodeConn ends Finset.univ x y) (i : ℕ∞)
        ≤ localNodeConn ends (upto (σ K) i) x y := by sorry

end NagamochiIbaraki.NodeConn
