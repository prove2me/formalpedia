-- Prove2me | Theorems.Thm_InducedMinorDeletion1657_Main_torso_sparsity
-- name    : InducedMinorDeletion1657.Main.torso_sparsity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:35:09.737767+00:00
-- url     : https://prove2.me/theorems/af6da34f-a33c-4349-bc35-62f7d641ec37
-- title:
--   Lemma 4.9 — torso sparsity
-- statement:
--   For fixed $H$, there is a positive constant $C$, independent of $G,M,d,\Delta$, such that an $H$-induced-minor-free graph $G$ with a $d$-core $M$ and $\Delta$-degenerate $G[M]$ satisfies
--   $$|E(\operatorname{Torso}(G,M))|-|E(G)|\le C(d+\Delta)|M|.$$
--   Here $d$ is positive, as in the source definition of a core, and the degeneracy bound $\Delta$ is nonnegative. Since the torso retains every original edge, the natural subtraction counts exactly the added edges. This bounds densification of the torso uniformly.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → graphs on Fin n, including n = 0; nonnegative treewidth from actual decompositions; reason: finite relabeling preserves every instance; empty treewidth zero changes no nonnegative-width predicate
--   - reading: no explicit domain for the structural degeneracy bound Δ → all nonnegative integer Δ, with d positive as in the core definition; reason: zero degeneracy is meaningful; this stronger reading excludes no source instance
--   - encoding: O((d+Δ)|M|) with constant depending only on H → ∃ positive natural C before all G,M,d,Δ; natural edge-count subtraction; reason: a natural ceiling absorbs the unknown real constant; all original edges are retained, so subtraction is exact
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), p. 22 (PDF p. 23), Lemma 4.9

import Definitions.Def_InducedMinorDeletion1657_Main_Collections

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main

/-- Lemma 4.9, printed p. 22 / PDF p. 23. See the local source audit for conventions. -/
theorem torso_sparsity :
∀ H : InputGraph, ∃ C : ℕ, 0 < C ∧
  ∀ (G : InputGraph) (M : Finset (Fin G.n)) (d Δ : ℕ),
    0 < d → excluded H.graph G.graph → core G.graph M d →
    ForestBackdoorFPT.IsDegenerate (G.graph.induce (↑M : Set (Fin G.n))) Δ →
    edges (torso G.graph M) - edges G.graph ≤ C * (d + Δ) * M.card := by sorry

end InducedMinorDeletion1657.Main
