-- Prove2me | Theorems.Thm_InducedMinorDeletion1657_Main_auxiliary_minor_free
-- name    : InducedMinorDeletion1657.Main.auxiliary_minor_free
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:35:14.537299+00:00
-- url     : https://prove2.me/theorems/6a0c6328-5de6-40eb-9e5f-910dd5a84b88
-- title:
--   Lemma 3.12 — auxiliary graph is ordinary-minor-free
-- statement:
--   Let $G$ exclude $H$ as an induced minor, and let $I$ be independent. Define $G_I$ on vertex set $I$, with an edge $uv$ precisely when some component $C$ of $G-I$ has the entire external neighborhood $N_G(V(C))=\{u,v\}$. Then
--   $$G_I\text{ excludes }H\text{ as an ordinary minor}.$$
--   This connects the auxiliary construction to ordinary-minor sparsity bounds. Requiring equality of the neighborhood, rather than containment of the pair, is essential.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → graphs on Fin n, including n = 0; nonnegative treewidth from actual decompositions; reason: finite relabeling preserves every instance; empty treewidth zero changes no nonnegative-width predicate
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), p. 15 (PDF p. 16), Lemma 3.12

import Definitions.Def_InducedMinorDeletion1657_Main_Collections

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main

/-- Lemma 3.12, printed p. 15 / PDF p. 16. See the local source audit for conventions. -/
theorem auxiliary_minor_free :
∀ (H G : InputGraph) (I : Finset (Fin G.n)),
  excluded H.graph G.graph → independent G.graph I →
  ¬ ordinaryMinor H.graph (auxiliary G.graph I) := by sorry

end InducedMinorDeletion1657.Main
