-- Prove2me | Theorems.Thm_InducedMinorDeletion1657_Main_degenerate_core_treewidth
-- name    : InducedMinorDeletion1657.Main.degenerate_core_treewidth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:35:05.593639+00:00
-- url     : https://prove2.me/theorems/9adf7208-dfd6-41ef-84bd-1f8b30c129f2
-- title:
--   Corollary 4.10 — treewidth from a degenerate core
-- statement:
--   For each fixed $H$, one positive constant $C$ works for every $H$-induced-minor-free graph $G$, a positive integer $d$, nonnegative integers $\Delta,t$, and a $d$-core $M$ such that $G[M]$ is $\Delta$-degenerate and $\operatorname{tw}(G-M)\le t$:
--   $$\operatorname{tw}(G)\le C\left(t+\sqrt{(d+\Delta)|M|}\right).$$
--   The parameter $t$ is outside the square root. The statement quantifies over every witnessing core, which is equivalent to the source's implication from existence of such a core. This is the structural width bound used in sublinear branching.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → graphs on Fin n, including n = 0; nonnegative treewidth from actual decompositions; reason: finite relabeling preserves every instance; empty treewidth zero changes no nonnegative-width predicate
--   - reading: no explicit domains for the structural bounds Δ,t → all nonnegative integer Δ,t, with d positive as in the core definition; reason: zero degeneracy and residual treewidth are meaningful; this stronger reading excludes no source instance
--   - encoding: existence of a d-core M and O(t+√((d+Δ)|M|)) → every witnessing M with one positive natural C before G,M,d,Δ,t; reason: equivalent witness-wise statement with all constant dependence made explicit
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), p. 23 (PDF p. 24), Corollary 4.10

import Definitions.Def_InducedMinorDeletion1657_Main_Collections

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main

/-- Corollary 4.10, printed p. 23 / PDF p. 24. See the local source audit for conventions. -/
theorem degenerate_core_treewidth :
∀ H : InputGraph, ∃ C : ℕ, 0 < C ∧
  ∀ (G : InputGraph) (M : Finset (Fin G.n)) (d Δ t : ℕ),
    0 < d → excluded H.graph G.graph → core G.graph M d →
    ForestBackdoorFPT.IsDegenerate (G.graph.induce (↑M : Set (Fin G.n))) Δ →
    modulator G.graph t M →
    (width G.graph : ℝ) ≤ C * ((t : ℝ) + Real.sqrt (((d : ℝ) + Δ) * M.card)) := by sorry

end InducedMinorDeletion1657.Main
