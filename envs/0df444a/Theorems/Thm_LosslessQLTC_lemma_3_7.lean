-- Prove2me | Theorems.Thm_LosslessQLTC_lemma_3_7
-- name    : LosslessQLTC.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:22:27.483172+00:00
-- url     : https://prove2.me/theorems/54ed3282-dea7-4929-b5de-00f2d3aa9af9
-- title:
--   Lemma 3.7, p.24 — $\varphi$ embeds $G$ in the complete multipartite complex
-- statement:
--   Let $v\in V_\emptyset$, and let $M$ be the complete $k$-partite simplicial complex whose $j$-th part is $\mathrm{Lk}_{\{j\}}(v)$. The map $\varphi:G\to M$, $\varphi(x_I)=\{x_{\{j\}}\in\mathrm{Lk}_{\{j\}}(v):x_{\{j\}}\le x_I,\ j\in I\}$, is a type-preserving poset isomorphism between $G$ and its image. This is the comparison through which multipartite expansion passes to the link.
--
--   Differences from the source:
--   - encoding: a decorated $(k,2)$-cubical complex with blocks $V_I$ and cubes $X(i)$ for all $i$, directions $1,\dots,k$ → `SquareComplex k`: one vertex type with a type map, the graph and $X(2)$ only, directions `Fin k`; reason: $X(0),X(1)$ are forced, no result uses $X(i)$ for $i\ge3$, and any such data extends with $X(i)=\emptyset$ for $i\ge3$
--   - encoding: $\varphi(x_I)$ as a face of $M$ with order by inclusion → $\varphi(x_I)$ as a vertex set, with the clauses: one vertex in each part indexed by $\mathrm{type}(x)$, nothing else, injective on $G$, and $\varphi(x)\subseteq\varphi(y)\iff x\le y$; reason: the same assertion, spelled out
--   - encoding: the reference ordering of each type $I$ is fixed arbitrarily → the increasing ordering of $I$; reason: Lemma 3.3 makes the fiber size independent of the ordering
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Lemma 3.7, p.24

import Mathlib
import Definitions.Def_LosslessQLTC_Paths

namespace LosslessQLTC

/-- Lemma 3.7 (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.24): for `v ∈ V_∅`, the map
`φ : G → M` is a type-preserving poset isomorphism between `G` and its image.

**Formalization Note.** The first two clauses say that `φ(x)` is a face of `M` of type `type x`:
exactly one vertex in each part indexed by `j ∈ type x`, and no other vertices. The next two are
injectivity on `G` and preservation of the order in both directions, the order on faces of `M` being
inclusion. -/
theorem lemma_3_7 {k : ℕ} (X : SquareComplex k) (v : X.Vtx) (hv : X.type v = ∅) :
    (∀ x ∈ goodSet X v, ∀ j ∈ X.type x, ∃! y, y ∈ phi X v x ∧ y ∈ LkType X v {j}) ∧
    (∀ x ∈ goodSet X v, ∀ y ∈ phi X v x, ∃ j ∈ X.type x, y ∈ LkType X v {j}) ∧
    (∀ x ∈ goodSet X v, ∀ y ∈ goodSet X v, phi X v x = phi X v y → x = y) ∧
    (∀ x ∈ goodSet X v, ∀ y ∈ goodSet X v,
      (phi X v x ⊆ phi X v y ↔ Relation.ReflTransGen X.up x y)) := by sorry

end LosslessQLTC
