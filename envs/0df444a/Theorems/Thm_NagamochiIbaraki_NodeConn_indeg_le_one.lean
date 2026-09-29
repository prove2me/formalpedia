-- Prove2me | Theorems.Thm_NagamochiIbaraki_NodeConn_indeg_le_one
-- name    : NagamochiIbaraki.NodeConn.indeg_le_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:09:19.056792+00:00
-- url     : https://prove2.me/theorems/604e6b78-d5ae-4860-a54d-8905109a0a17
-- title:
--   In-degree at most one (§2, p. 588): orienting FOREST's edges by scan order, each class E*_i has at most one arc into any node
-- statement:
--   Let $G = (V, E)$ be a graph with $|V| \ge 2$ and no self-loop, and consider a completed run of Procedure FOREST on $G$. Orient every edge $e = (u, v)$ as the arc $u \to v$ when $u$ is scanned before $v$ (equivalently, when $e$ is scanned while $u$ is the current node). Then at every time instant of the run, for every class index $1 \le i \le |E|$ and every node $v$,
--
--   $$
--   \bigl|\{\, e \in E^*_i : e = (u, v) \text{ for some node } u \text{ scanned before } v \,\}\bigr| \le 1 ,
--   $$
--
--   that is, in the directed graph $\vec E^*_i$ every node has in-degree at most one.
--
--   The paper derives this from the fact that each nontrivial tree of $(V, E_i)$, oriented in this way, is a rooted out-tree. The Appendix proof of Lemma 3.1 and the proof of Lemma 3.2 use it repeatedly.
--
--   **Formalization Note** "Scanned before" is read on the selection order of the completed run, in which each node occurs exactly once. In-degree at most one is stated as: two edges of $E^*_i$ that both enter $v$ from earlier-scanned nodes are equal. The same paragraph of the paper also notes that the whole oriented graph is acyclic; this holds by construction once arcs follow a linear order and is not stated separately.
-- source:
--   Nagamochi, Ibaraki, A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph, Algorithmica 7 (1992), p. 588, §2, orientation paragraph (second paragraph): indeg(v) of T⃗ is at most one

import Mathlib
import Definitions.Def_NagamochiIbaraki_NodeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_NodeConn_Forest

namespace NagamochiIbaraki.NodeConn

theorem indeg_le_one
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsCompletedRun ends σ K) :
    ∀ k, k ≤ K → ∀ (i : ℕ) (v : V), 1 ≤ i → i ≤ Fintype.card E →
      ∀ e₁ ∈ cls (σ k) i, ∀ e₂ ∈ cls (σ k) i, ∀ u₁ u₂ : V,
        ends e₁ = s(u₁, v) → scanBefore (σ K) u₁ v →
        ends e₂ = s(u₂, v) → scanBefore (σ K) u₂ v → e₁ = e₂ := by sorry

end NagamochiIbaraki.NodeConn
