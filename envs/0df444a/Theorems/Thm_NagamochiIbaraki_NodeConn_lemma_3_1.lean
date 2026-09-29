-- Prove2me | Theorems.Thm_NagamochiIbaraki_NodeConn_lemma_3_1
-- name    : NagamochiIbaraki.NodeConn.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:09:48.944518+00:00
-- url     : https://prove2.me/theorems/2c7536f0-b2fd-407f-90bc-cf087cf49bd5
-- title:
--   Lemma 3.1 — an x–y path in E*_j through w forces any w–x and w–y paths in E*_i (i < j) to meet outside w
-- statement:
--   Let $G = (V, E)$ be a simple graph with $|V| \ge 2$, and consider a completed run of Procedure FOREST on $G$. Fix a time instant and indices $1 \le i < j \le |E|$, and let $E^*_i, E^*_j$ be the classes at that instant. Suppose there is a path $P_j \subseteq E^*_j$ from $x$ to $y$ whose nodes, in order, are
--
--   $$
--   x,\ u_1,\ u_2,\ \dots,\ u_k = w,\ y \qquad (k \ge 1),
--   $$
--
--   such that either $k = 1$, or $k \ge 2$ and $u_1$ is scanned before $w$. If $P_i \subseteq E^*_i$ is a path from $w$ to $x$ and $P'_i \subseteq E^*_i$ is a path from $w$ to $y$, then $P_i$ and $P'_i$ have a common node other than $w$.
--
--   This is the key structural fact about FOREST for node-connectivity: it is the contradiction reached in both steps of the induction proving Lemma 3.2.
--
--   **Formalization Note** The path $P_j$ is a Mathlib path in $(V, E^*_j)$ whose list of nodes is $x$, then the nonempty list $u_1, \dots, u_k$ with last element $w$, then $y$. "Scanned before" is read on the selection order of the completed run; under the lemma's hypotheses $w$ has already been chosen at the instant considered, so this agrees with the order at that instant.
-- source:
--   Nagamochi, Ibaraki, A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph, Algorithmica 7 (1992), p. 591, Lemma 3.1 and display (3.2); proof in the Appendix, p. 595

import Mathlib
import Definitions.Def_NagamochiIbaraki_NodeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_NodeConn_Forest

namespace NagamochiIbaraki.NodeConn

theorem lemma_3_1
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (hsimple : Function.Injective ends)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsCompletedRun ends σ K)
    (n : ℕ) (hn : n ≤ K) (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ Fintype.card E)
    (x y w : V) (us : List V) (hus : us ≠ []) (hw : us.getLast hus = w)
    (p : (edgeGraph ends (cls (σ n) j)).Walk x y) (hp : p.IsPath)
    (hps : p.support = x :: us ++ [y])
    (hord : us.length = 1 ∨ scanBefore (σ K) (us.head hus) w)
    (q : (edgeGraph ends (cls (σ n) i)).Walk w x) (hq : q.IsPath)
    (q' : (edgeGraph ends (cls (σ n) i)).Walk w y) (hq' : q'.IsPath) :
    ∃ z : V, z ≠ w ∧ z ∈ q.support ∧ z ∈ q'.support := by sorry

end NagamochiIbaraki.NodeConn
