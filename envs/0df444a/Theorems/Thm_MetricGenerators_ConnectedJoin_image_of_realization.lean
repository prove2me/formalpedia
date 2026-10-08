-- Prove2me | Theorems.Thm_MetricGenerators_ConnectedJoin_image_of_realization
-- name    : MetricGenerators.ConnectedJoin.image_of_realization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:49:40.564863+00:00
-- url     : https://prove2.me/theorems/615d5c23-3e58-429a-8774-e18f9a34855e
-- title:
--   Proof of Theorem 6, p. 392 — the image F of the tree A under the isometry is a T-join and a tree with μ_F = μ_G on V(F)
-- statement:
--   Let $G$ be a connected finite graph and $T\subseteq V(G)$ nonempty. Let $A$ be a tree, $g:T\to V(A)$ a map, and $T'=g(T)$. Suppose
--
--   1. $A$ is a $T'$-join: a vertex of $A$ has odd degree in $A$ exactly when it lies in $T'$;
--   2. $\varphi:V(A)\to V(G)$ is an isometry from $A$ to $G$, i.e. $\mu_G(\varphi(a),\varphi(b))=d_A(a,b)$ for all $a,b$, extending the inverse of $g$: $\varphi(g(t))=t$ for all $t\in T$.
--
--   Let $F=\{\varphi(a)\varphi(b): ab\in E(A)\}$ be the image of $A$ in $G$. Then
--
--   $$F\ \text{is a }T\text{-join of }G,\qquad F\ \text{is a tree},\qquad \mu_F(x,y)=\mu_G(x,y)\ \text{for all }x,y\in V(F).$$
--
--   In the proof of Theorem 6 these are exactly the hypotheses of Lemma 2, which then shows that $F$ is a connected minimum $T$-join.
--
--   **Formalization Note.** "$f:T'\to T$ is the inverse of $g$" and "$\varphi$ extends $f$" are encoded together as $\varphi(g(t))=t$. It is not assumed that $g$ realizes $\mu_G|_T$; that follows from the other hypotheses. The hypothesis $T\neq\emptyset$ is the one Theorem 6 carries: for $T=\emptyset$ the tree $A$ may be a single vertex, and then $F=\emptyset$ is not a tree.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 392, §3.2, proof of Theorem 6 (unnumbered)

import Mathlib
import Definitions.Def_MetricGenerators_ConnectedJoin_TJoin
import Definitions.Def_MetricGenerators_ConnectedJoin_TreeMetric

namespace MetricGenerators.ConnectedJoin

/-- **Proof of Theorem 6, p. 392 (unnumbered).** "Let F be the image of A in G provided by the
isometry of the third condition. Then by the second condition, F is a T-join, and since it is a
tree, it is connected. Now we see from this construction that the condition of Lemma 2 is
satisfied: μ_F arises from μ_G|T by two isometries." (Sebő and Tannier, On Metric Generators of
Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 392.)

Let `G` be a connected graph, `T` a nonempty vertex set, `A` a tree on `Fin N`, `g : T → V(A)`,
and suppose `A` is a `g(T)`-join and `φ : V(A) → V(G)` is an isometry from `A` to `G` extending
the inverse of `g` (`φ (g t) = t`). Let `F` be the image of the edges of `A` under `φ`. Then `F`
is a `T`-join of `G`, the graph `(V(F), F)` is a tree, and the distance in `(V(F), F)` between any
two vertices of `V(F)` equals their distance in `G`.

**Formalization Note.** "Isometry from A to G" is distance preservation for all pairs of vertices
of `A`. "f is the inverse of g" and "extending f" are encoded together as `φ (g t) = t`. The
hypothesis `T.Nonempty` is the standing nonemptiness of Theorem 6 (see `theorem_6`); without it
`A` may be a single vertex and `F = ∅`, which is not a tree. That `g` realizes μ_G|T is not
assumed: it follows from the isometry and `φ (g t) = t`. -/
theorem image_of_realization {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : G.Connected) (T : Finset V) (hT : T.Nonempty) {N : ℕ} (A : SimpleGraph (Fin N))
    [DecidableRel A.Adj] (hA : A.IsTree) (g : ↥T → Fin N) (hjoin : GraphIsJoin A (Set.range g))
    (φ : Fin N → V) (hφ : ∀ a b : Fin N, G.dist (φ a) (φ b) = A.dist a b)
    (hext : ∀ t : ↥T, φ (g t) = ↑t) :
    MetricGenerators.FewComponents.IsTJoin G T (A.edgeFinset.image (Sym2.map φ)) ∧
      IsTreeEdgeSet (A.edgeFinset.image (Sym2.map φ)) ∧
      ∀ x ∈ MetricGenerators.FewComponents.edgeSupport (A.edgeFinset.image (Sym2.map φ)),
        ∀ y ∈ MetricGenerators.FewComponents.edgeSupport (A.edgeFinset.image (Sym2.map φ)),
          edgeDist (A.edgeFinset.image (Sym2.map φ)) x y = G.dist x y := by sorry

end MetricGenerators.ConnectedJoin
