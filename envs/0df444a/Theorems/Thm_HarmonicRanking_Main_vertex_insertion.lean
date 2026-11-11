-- Prove2me | Theorems.Thm_HarmonicRanking_Main_vertex_insertion
-- name    : HarmonicRanking.Main.vertex_insertion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:22.799803+00:00
-- url     : https://prove2.me/theorems/74cc67bc-cd3b-4b26-8c9a-e81916a41997
-- title:
--   Lemma 3.4 — insertion in a common bipartite edge order
-- statement:
--   Let $E\subseteq L\times R$ be any finite bipartite graph, $v\in R$, and $z\in L$. Fix any total scan order, without a score restriction. Let $E-v$ discard the pairs incident to $v$. For every common prefix of length $n$,
--
--   $$
--   z\text{ is matched by greedy on }E-v\text{ in that prefix}
--   \quad\Longrightarrow\quad
--   z\text{ is matched by greedy on }E\text{ in that prefix}.
--   $$
--
--   Equivalently, whenever the reduced run selects the edge matching $z$, the full run has already matched $z$ by that scan point. This is the source's vertex-insertion comparison, independent of harmonic priorities.
--
--   Differences from the source:
--   - encoding: arbitrary disjoint finite vertex sets → arbitrary finite types with their disjoint sum and all potential pairs; reason: every source instance is represented, including empty sides, empty realizations and zero weights
--   - encoding: a common total order on realized graph edges, skipping deleted-vertex edges in the reduced run → a common total order on all potential pairs, with unrealized and deleted pairs acting as no-ops; every prefix is compared; reason: any source order extends to potential pairs and every accepted realized prefix has identical matching status
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF p. 12, Lemma 3.4

import Definitions.Def_HarmonicRanking_Main_Scan

set_option autoImplicit false

namespace HarmonicRanking.Main

theorem vertex_insertion
    {L R : Type*} [Fintype L] [Fintype R]
    (E : Finset (L × R)) (o : ScanOrder L R) (v : R) (z : L) (n : ℕ) :
    (∃ e ∈ greedy (withoutRight E v) (o.edges.take n), e.1 = z) →
    ∃ e ∈ greedy E (o.edges.take n), e.1 = z := by sorry

end HarmonicRanking.Main
