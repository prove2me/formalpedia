-- Prove2me | Theorems.Thm_NagamochiIbaraki_EdgeConn_forest_partition_theorem_2_1
-- name    : NagamochiIbaraki.EdgeConn.forest_partition_theorem_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:05:24.565974+00:00
-- url     : https://prove2.me/theorems/bfb8c193-b9f3-4ed1-a8e9-b3f5609dcabe
-- title:
--   Theorem 2.1 — FOREST partitions E into E_1, …, E_|E| satisfying (2.1), with |E_i| ≤ |V| − 1, and |E_i| ≤ |V| − i, E_i = ∅ (i ≥ |V|) if G is simple
-- statement:
--   Let $G = (V, E)$ be a finite undirected graph with $|V| \ge 2$ nodes and no self-loop, possibly with multiple edges. Run Procedure FOREST on $G$ to completion, with any choices of ties at line 5 and of edge order at line 6, and let $E_1, E_2, \dots, E_{|E|}$ be the classes it outputs; write $G_i = (V, E_1 \cup \cdots \cup E_i)$ and let $\lambda(x, y; H)$ denote local edge-connectivity. Then:
--
--   1. **Partition.** Every edge of $G$ lies in exactly one class $E_i$ with $1 \le i \le |E|$.
--   2. **Connectivity (2.1).** For every $i = 1, 2, \dots, |E|$,
--   $$
--   \lambda(x, y; G_i) \;\ge\; \min\{\lambda(x, y; G),\ i\} \qquad \text{for all } x, y \in V .
--   $$
--   3. **Size, multiple graphs.** $|E_i| \le |V| - 1$ for $i = 1, 2, \dots, |E|$.
--   4. **Size, simple graphs.** If $G$ is simple, then $|E_i| \le |V| - i$ for $i = 1, 2, \dots, |V| - 1$, and $|E_i| = 0$ for $i = |V|, \dots, |E|$.
--
--   Consequently, for every $k$, the subgraph $G_k$ preserves all local edge-connectivities up to $k$ while having at most $k(|V|-1)$ edges, and at most $k|V| - k(k+1)/2$ edges when $G$ is simple: a sparse certificate of $k$-edge-connectivity computed by one graph search.
--
--   **Formalization Note** The paper's Theorem 2.1 also asserts that the partition "is found in O(|V| + |E|) time"; the running time is not formalized (there is no machine model), and only the structural conclusions are stated. The execution is a completed run $\sigma_0, \dots, \sigma_K$ of the nondeterministic step relation encoding FOREST, and the classes are read off its final state; the theorem holds for every such run. The paper's "if $G$ is multiple" bound $|E_i| \le |V| - 1$ is stated for every loopless graph, simple or not. Simplicity is injectivity of the end-node map. Local edge-connectivity takes values in `ℕ∞` and is $\infty$ at $x = y$.
-- source:
--   Nagamochi, Ibaraki, A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph, Algorithmica 7 (1992), pp. 588–589, Theorem 2.1 (running time excluded)

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_EdgeConn_localEdgeConn
import Definitions.Def_NagamochiIbaraki_EdgeConn_Forest

namespace NagamochiIbaraki.EdgeConn

theorem forest_partition_theorem_2_1
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsCompletedRun ends σ K) :
    (∀ e : E, 1 ≤ (σ K).idx e ∧ (σ K).idx e ≤ Fintype.card E) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card E → ∀ x y : V,
      min (localEdgeConn ends Finset.univ x y) (i : ℕ∞) ≤
        localEdgeConn ends (upto (σ K) i) x y) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card E →
      (cls (σ K) i).card ≤ Fintype.card V - 1) ∧
    (Function.Injective ends →
      (∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card V - 1 →
        (cls (σ K) i).card ≤ Fintype.card V - i) ∧
      (∀ i : ℕ, Fintype.card V ≤ i → i ≤ Fintype.card E → cls (σ K) i = ∅)) := by sorry

end NagamochiIbaraki.EdgeConn
