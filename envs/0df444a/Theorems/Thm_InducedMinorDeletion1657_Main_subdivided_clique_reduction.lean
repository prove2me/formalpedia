-- Prove2me | Theorems.Thm_InducedMinorDeletion1657_Main_subdivided_clique_reduction
-- name    : InducedMinorDeletion1657.Main.subdivided_clique_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:34:46.044197+00:00
-- url     : https://prove2.me/theorems/a4263568-3904-4ff3-b726-ab938f6ce564
-- title:
--   Lemma 3.11 — reduction to a subdivided clique
-- statement:
--   Let $H$ be any finite graph and $h=|V(H)|$. Let $K_h^\bullet$ subdivide each edge of the complete graph on $h$ vertices exactly once. Then
--   $$\mathcal G_H\subseteq\mathcal G_{K_h^\bullet}.$$
--   Thus every $H$-induced-minor-free graph excludes this particular subdivided clique as an induced minor. Empty and small excluded graphs are included. This permits the structural reduction without replacing induced minors by ordinary minors.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → graphs on Fin n, including n = 0; nonnegative treewidth from actual decompositions; reason: finite relabeling preserves every instance; empty treewidth zero changes no nonnegative-width predicate
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), p. 15 (PDF p. 16), Lemma 3.11

import Definitions.Def_InducedMinorDeletion1657_Main_Collections

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main

/-- Lemma 3.11, printed p. 15 / PDF p. 16. See the local source audit for conventions. -/
theorem subdivided_clique_reduction :
∀ (H G : InputGraph), excluded H.graph G.graph →
  excluded (subdividedClique H.n) G.graph := by sorry

end InducedMinorDeletion1657.Main
