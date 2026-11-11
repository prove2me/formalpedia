-- Prove2me | Theorems.Thm_IntervalExplore_KT1_lemma_1
-- name    : IntervalExplore.KT1.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:57.877437+00:00
-- url     : https://prove2.me/theorems/d8701991-c912-4015-a3ab-3a2fe995ae2a
-- title:
--   Lemma 1 — equality of known and visited sets certifies coverage
-- statement:
--   Let $G=(V,E)$ be a finite simple undirected graph with $n=|V|\ge3$ and $m=|E|\ge n$, and let every snapshot contain one common spanning tree. Fix any injective identifiers, fixed local port numbering and starting vertex, and any run of GreedyExp1, including every resolution of its closest-node and shortest-path choices.
--   At every time $t$, the known and visited sets satisfy
--   $$
--   V_{\rm map}(t)=V_{\rm vis}(t)\ \Longrightarrow\ V_{\rm vis}(t)=V.
--   $$
--   This is the coverage certificate used by the stopping rule. The model retains the final observation after termination, so the same assertion is well-defined for the frozen execution thereafter.
--
--   Differences from the source:
--   - encoding: vertices with unique identifiers and their exploration map → a finite carrier V, injective natural-number labels, an observation map on labels and its pullback to SimpleGraph V; reason: injective relabeling preserves all visited sets, edges and distances; vertices outside the known set are isolated
--   - encoding: GreedyExp1 with arbitrary closest-node and shortest-path choices → every observation-only policy satisfying IsGreedyAlgorithm; reason: the predicate specifies exactly Algorithm 1 decisions and no success property; every tie resolution along a run is represented by such a history policy
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), Lemma 1, p.6 (PDF p.7)

import Definitions.Def_IntervalExplore_KT1_GreedyMap

set_option autoImplicit false

namespace IntervalExplore.KT1

/-- Lemma 1, p.6 (PDF p.7), with the common-tree standing assumption. -/
theorem lemma_1 {V : Type} [Fintype V] [DecidableEq V] (W : World V)
    (A : Alg) (hA : IsGreedyAlgorithm A)
    (hn : 3 ≤ Fintype.card V) (hm : Fintype.card V ≤ edgeCount W.graph)
    (htree : CommonTree W.dynamic) (t : ℕ) :
    worldKnown W A t = worldVisited W A t → worldVisited W A t = Finset.univ := by sorry

end IntervalExplore.KT1
