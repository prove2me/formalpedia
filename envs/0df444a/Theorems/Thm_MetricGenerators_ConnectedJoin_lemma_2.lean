-- Prove2me | Theorems.Thm_MetricGenerators_ConnectedJoin_lemma_2
-- name    : MetricGenerators.ConnectedJoin.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:49:25.511988+00:00
-- url     : https://prove2.me/theorems/613fbc94-95ad-474c-85fe-d110a350ae78
-- title:
--   Lemma 2 — a connected T-join F is minimum iff it is a tree and μ_F = μ_G on V(F)
-- statement:
--   Let $G$ be a connected finite graph, $T\subseteq V(G)$, and let $F$ be a connected $T$-join of $G$. Then $F$ is a minimum $T$-join if and only if
--
--   $$F\ \text{is a tree}\qquad\text{and}\qquad \mu_F(x,y)=\mu_G(x,y)\quad\text{for all }x,y\in V(F),$$
--
--   where $\mu_G$ and $\mu_F$ are the shortest-path distances in $G$ and in the graph $(V(F),F)$.
--
--   This is the link between $T$-joins and tree metrics: a connected minimum $T$-join is a tree embedded isometrically in $G$, and conversely. Theorem 6 is deduced from it.
--
--   **Formalization Note.** $G$ connected is the paper's standing assumption. Connectivity and the tree property are those of $(V(F),F)$. The evenness of $|T|$ is not a separate hypothesis, since it follows from the existence of a $T$-join.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 392, Lemma 2

import Mathlib
import Definitions.Def_MetricGenerators_ConnectedJoin_TJoin

namespace MetricGenerators.ConnectedJoin

/-- **Lemma 2** (p. 392). "A connected T-join F in a graph G is minimum if and only if it is a
tree, and for all x, y ∈ V(F): μ_F(x, y) = μ_G(x, y)." (Sebő and Tannier, On Metric Generators of
Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 392, Lemma 2.)

Let `G` be a connected graph and `F` a connected `T`-join of `G`. Then `F` is a minimum `T`-join
if and only if the graph `(V(F), F)` is a tree and the distance in `(V(F), F)` between any two
vertices of `V(F)` equals their distance in `G`.

**Formalization Note.** `G.Connected` is the paper's standing assumption (p. 383). Connectivity
and the tree property refer to the graph `(V(F), F)` (`IsConnectedEdgeSet`, `IsTreeEdgeSet`), and
μ_F is `edgeDist F` (the distance in `(V(F), F)` for vertices of `V(F)`). The evenness of `|T|` is
not a separate hypothesis: it follows from the existence of the `T`-join `F`. -/
theorem lemma_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : G.Connected)
    (T : Finset V) (F : Finset (Sym2 V)) (hF : MetricGenerators.FewComponents.IsTJoin G T F) (hconn : IsConnectedEdgeSet F) :
    MetricGenerators.FewComponents.IsMinTJoin G T F ↔
      IsTreeEdgeSet F ∧
        ∀ x ∈ MetricGenerators.FewComponents.edgeSupport F, ∀ y ∈ MetricGenerators.FewComponents.edgeSupport F, edgeDist F x y = G.dist x y := by sorry

end MetricGenerators.ConnectedJoin
