-- Prove2me | Theorems.Thm_GeomDL_WL_iso_identical_outputs
-- name    : GeomDL.WL.iso_identical_outputs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:56.541995+00:00
-- url     : https://prove2.me/theorems/1e00efd2-2abc-4f5c-86a0-66e64bd0ce73
-- title:
--   Side-note p. 119 — GNNs attach identical representations to isomorphic graphs
-- statement:
--   Let $N$ be a message-passing GNN with constant initial features, and let $G$, $G'$ be graphs with an isomorphism $e : V(G) \to V(G')$, a bijection with $(u, v) \in E(G) \iff (e(u), e(v)) \in E(G')$. Then for every round $t$ and every node $u$ of $G$,
--   $$
--   h^t_{G}(u) = h^t_{G'}(e(u)),
--   $$
--   and for every read-out function and every depth $T$ the graph-level outputs coincide:
--   $$
--   \mathrm{readout}\big(\{\!\{h^T_G(u)\}\!\}_{u \in V(G)}\big) = \mathrm{readout}\big(\{\!\{h^T_{G'}(v)\}\!\}_{v \in V(G')}\big).
--   $$
--
--   This is the reason the book calls the isomorphic case of graph isomorphism "trivially solved" by GNNs: they never separate isomorphic graphs.
--
--   **Formalization Note** Mission IX states this for the message-passing layer (35); mission II states the analogous fact for permutation-invariant and equivariant functions in a different encoding.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), Ch. 7, side-note p. 119; §4.1, p. 35, "permutation invariant and equivariant functions produce identical outputs on isomorphic (topologically-equivalent) graphs"

import Mathlib
import Definitions.Def_WLIdentification
import Definitions.Def_GeomDL_WL_Defs

namespace GeomDL.WL
open OAI.WLIdentification

/-- Side-note p. 119 (with §4.1, p. 35): a message-passing GNN attaches identical representations to
isomorphic graphs. If `e` is an adjacency-preserving bijection from the nodes of `G` to those of
`G'`, then every node feature is carried along `e` at every round, and every read-out of the final
features agrees on `G` and `G'`. -/
theorem iso_identical_outputs {F M A Y : Type*} (N : GNN F M A) (G G' : Graph)
    (e : Fin G.order ≃ Fin G'.order) (he : ∀ u v, G.edge u v = G'.edge (e u) (e v)) :
    (∀ t u, N.features G t u = N.features G' t (e u)) ∧
      ∀ (readout : Multiset F → Y) (T : ℕ), N.output readout G T = N.output readout G' T := by sorry

end GeomDL.WL
