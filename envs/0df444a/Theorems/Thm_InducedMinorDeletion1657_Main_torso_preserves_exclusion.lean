-- Prove2me | Theorems.Thm_InducedMinorDeletion1657_Main_torso_preserves_exclusion
-- name    : InducedMinorDeletion1657.Main.torso_preserves_exclusion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:34:41.916488+00:00
-- url     : https://prove2.me/theorems/21bba7ea-541d-4f4a-aa46-fa923ebe9e01
-- title:
--   Lemma 4.8 — torso preserves induced-minor exclusion
-- statement:
--   For every finite graph $H$ there exists one finite graph $H'$ such that, for every $H$-induced-minor-free graph $G$ and every independent vertex set $I$,
--   $$\operatorname{Torso}(G,V(G)\setminus I)\in\mathcal G_{H'}.$$
--   The excluded graph $H'$ depends only on $H$, not on $G$ or $I$. The torso retains the vertices of $I$ and all original edges. This is the full source exclusion guarantee.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → graphs on Fin n, including n = 0; nonnegative treewidth from actual decompositions; reason: finite relabeling preserves every instance; empty treewidth zero changes no nonnegative-width predicate
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), p. 21 (PDF p. 22), Lemma 4.8

import Definitions.Def_InducedMinorDeletion1657_Main_Collections

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main

/-- Lemma 4.8, printed p. 21 / PDF p. 22. See the local source audit for conventions. -/
theorem torso_preserves_exclusion :
∀ H : InputGraph, ∃ H' : InputGraph, ∀ (G : InputGraph) (I : Finset (Fin G.n)),
  excluded H.graph G.graph → independent G.graph I →
  excluded H'.graph (torso G.graph (Finset.univ \ I)) := by sorry

end InducedMinorDeletion1657.Main
