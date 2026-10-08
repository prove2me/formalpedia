-- Prove2me | Theorems.Thm_NashWilliams61_TreePacking_theorem_1
-- name    : NashWilliams61.TreePacking.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:57.705003+00:00
-- url     : https://prove2.me/theorems/b0871f54-8886-4677-9f40-942607a6b14a
-- title:
--   Theorem 1 — $G$ has $k$ edge-disjoint spanning trees iff $|E_P(G)| \ge k(|P|-1)$ for every partition $P$
-- statement:
--   Let $G$ be a finite unoriented multigraph without loops (parallel edges allowed) on a non-empty vertex set $V$, and let $k$ be a positive integer. For a partition $P$ of $V$ let $E_P(G)$ be the set of edges whose ends lie in different members of $P$. Then $G$ has $k$ pairwise edge-disjoint spanning trees if and only if
--   $$|E_P(G)| \ge k\,(|P| - 1) \qquad \text{for every partition } P \text{ of } V. \tag{1}$$
--
--   This is the tree-packing theorem, proved independently by Tutte (1961) and Nash-Williams (1961). It characterises the maximum number of edge-disjoint spanning trees by a min-max formula over vertex partitions and underlies the theory of matroid base packing.
--
--   **Formalization Note** $V$ is assumed non-empty (the paper's graphs have a vertex; on an empty vertex set no tree exists while (1) holds). The $k$ trees are a family indexed by $\{1, \dots, k\}$ with pairwise disjoint edge sets, each a spanning tree of $G$ in the multigraph sense. The inequality (1) is in $\mathbb Z$ and is required for every partition, including the one-part partition and the partition into singletons.
-- source:
--   Nash-Williams, Edge-disjoint spanning trees of finite graphs, J. London Math. Soc. 36 (1961), p. 445, Theorem 1, Eq. (1)

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NashWilliams61_TreePacking_Graphs
open NagamochiIbaraki.EdgeConn

namespace NashWilliams61.TreePacking

/-- **Theorem 1** (Nash-Williams 1961, p. 445). A finite loopless multigraph `G` on a
non-empty vertex set has `k` edge-disjoint spanning trees if and only if
`|E_P(G)| ≥ k(|P| − 1)` for every partition `P` of `V(G)`. -/
theorem theorem_1 {V E : Type} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype E]
    [DecidableEq E] (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag) (k : ℕ) (hk : 0 < k) :
    (∃ T : Fin k → Finset E, (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧
        ∀ i, IsSpanningTree ends (T i)) ↔
      ∀ P : Finpartition (Finset.univ : Finset V),
        (k : ℤ) * ((P.parts.card : ℤ) - 1) ≤ ((crossing ends P).card : ℤ) := by sorry

end NashWilliams61.TreePacking
