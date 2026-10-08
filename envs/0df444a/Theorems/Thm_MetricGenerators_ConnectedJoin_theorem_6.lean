-- Prove2me | Theorems.Thm_MetricGenerators_ConnectedJoin_theorem_6
-- name    : MetricGenerators.ConnectedJoin.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:49:36.847143+00:00
-- url     : https://prove2.me/theorems/3e5de1b7-a20e-42ff-86e0-cd4bbfc30516
-- title:
--   Theorem 6 — a connected minimum T-join exists iff μ_G|T is a tree metric whose minimal realization A is a T′-join and embeds isometrically in G extending f
-- statement:
--   Let $G$ be a connected finite graph and let $T\subseteq V(G)$ be a nonempty set of vertices of even cardinality. Write $\mu_G$ for the shortest-path distance of $G$ and $\mu_G|_T$ for its restriction to $T$. Then $G$ has a $T$-join that is both **minimum** and **connected** if and only if all of the following hold:
--
--   1. $\mu_G|_T$ is a tree metric; let $A$ be its (inclusionwise) minimal realization, $g$ the isometry from $(T,\mu_G|_T)$ to $A$, $T'=g(T)$, and $f:T'\to T$ the inverse of $g$;
--   2. the tree $A$ is a $T'$-join, i.e. a vertex of $A$ has odd degree exactly when it lies in $T'$;
--   3. there is an isometry $\varphi$ from $A$ to $G$ extending $f$:
--
--   $$\mu_G\bigl(\varphi(a),\varphi(b)\bigr)=d_A(a,b)\ \ \text{for all }a,b\in V(A),\qquad \varphi\bigl(g(t)\bigr)=t\ \ \text{for all }t\in T.$$
--
--   The theorem reduces the existence of a connected minimum $T$-join to a property of the metric $\mu_G|_T$ alone (conditions 1 and 2) plus an isometric embedding problem for a tree. In particular, if the minimal realization of $\mu_G|_T$ exists but is not a $T'$-join, no minimum $T$-join is connected.
--
--   **Formalization Note.** Conditions 2 and 3 are required of every inclusionwise minimal realization $(A,g)$; all of them are isomorphic by isomorphisms respecting $g$, so this is the paper's "$A$ denotes its unique minimal realization". The hypothesis $T\neq\emptyset$ is added: for $T=\emptyset$ the only minimum $T$-join is $\emptyset$, whose connectivity is a convention the paper does not discuss (with the convention used here, a connected graph has a vertex). Distances are natural numbers. A realization is a tree on $\mathrm{Fin}\,N$. A $T$-join is connected when the graph $(V(F),F)$ is connected.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 392, Theorem 6

import Mathlib
import Definitions.Def_MetricGenerators_ConnectedJoin_TJoin
import Definitions.Def_MetricGenerators_ConnectedJoin_TreeMetric

namespace MetricGenerators.ConnectedJoin

/-- **Theorem 6** (p. 392). "Let G be a connected graph, and let T be a subset of vertices of even
cardinality. There exists a connected minimum T-join in G if and only if all of the following
conditions hold:
• μ_G|T is a tree metric, A denotes its unique minimal realization, and g is the isometry from
(T, μ_G|T) to A, T′ := g(T); f : T′ → T is the inverse of g;
• The tree A is a T′-join;
• There exists an isometry from A to G extending f."
(Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004),
DOI 10.1287/moor.1030.0070, p. 392, Theorem 6.)

Let `G` be a connected finite graph and `T` a nonempty vertex set of even cardinality. There is a
`T`-join of `G` that is minimum and connected if and only if μ_G|T is a tree metric and, for every
inclusionwise minimal realization `(A, g)` of μ_G|T, (i) `A` is a `g(T)`-join and (ii) there is an
isometry `φ` from `A` to `G` with `φ (g t) = t` for every `t ∈ T`.

**Formalization Note.**
* "A denotes its unique minimal realization" is read as "for the minimal realization": conditions
  (i) and (ii) are required of **every** inclusionwise minimal realization. All of them are
  isomorphic by isomorphisms commuting with the realization maps (`minimal_realization_unique`),
  so this is the same as requiring them of one; but requiring them of *some* minimal realization
  would be a different reading in which the necessity half does not need the uniqueness.
* "f is the inverse of g" and "an isometry from A to G extending f" are encoded together as
  `φ (g t) = t`; an isometry preserves all distances.
* Added hypothesis `T.Nonempty`: for `T = ∅` the only minimum `T`-join is `∅`, whose
  connectivity is a convention the paper does not discuss; with Mathlib's convention (a connected
  graph has a vertex) the left side would be false and the right side true.
* Distances are `ℕ`-valued graph distances (`SimpleGraph.dist`); realizations are trees on `Fin N`
  (see `IsRealization`). Connectivity of `F` is connectivity of the graph `(V(F), F)`. -/
theorem theorem_6 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : G.Connected)
    (T : Finset V) (hT : Even T.card) (hTne : T.Nonempty) :
    (∃ F : Finset (Sym2 V), MetricGenerators.FewComponents.IsMinTJoin G T F ∧ IsConnectedEdgeSet F) ↔
      (IsTreeMetric (fun s t : ↥T => G.dist ↑s ↑t) ∧
        ∀ (N : ℕ) (A : SimpleGraph (Fin N)) (g : ↥T → Fin N),
          IsMinimalRealization (fun s t : ↥T => G.dist ↑s ↑t) A g →
            GraphIsJoin A (Set.range g) ∧
              ∃ φ : Fin N → V, (∀ a b : Fin N, G.dist (φ a) (φ b) = A.dist a b) ∧
                ∀ t : ↥T, φ (g t) = ↑t) := by sorry

end MetricGenerators.ConnectedJoin
