-- Prove2me | Theorems.Thm_IntervalExplore_KT1_lemma_2
-- name    : IntervalExplore.KT1.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:02.840287+00:00
-- url     : https://prove2.me/theorems/452ebbab-1ddb-4657-9358-bfe6a0ef8c0c
-- title:
--   Lemma 2 — exploration potential accounting
-- statement:
--   Let $G=(V,E)$ be a finite simple undirected graph with $n=|V|\ge3$ and $m=|E|\ge n$, and let every snapshot contain one common spanning tree. Fix any injective identifiers, fixed local port numbering and starting vertex, and any run of GreedyExp1, including every resolution of its closest-node and shortest-path choices.
--   Fix any order of edge eliminations within each move, and let $\iota_V$ and $\iota_E$ be the resulting charges. There exists a time $t\ge0$ with
--   $$
--   t\le n+\sum_{v\in V}\iota_V(v)+\sum_{e\in E}\iota_E(e),\qquad
--   V_{\rm map}(t)=V_{\rm vis}(t).
--   $$
--   The inequality uses integer arithmetic, retaining the charge $-1$ of the last newly visited vertex. This is the accounting bound connecting elapsed time to the separately bounded charges; eventual completion is not a hypothesis.
--
--   Differences from the source:
--   - encoding: vertices with unique identifiers and their exploration map → a finite carrier V, injective natural-number labels, an observation map on labels and its pullback to SimpleGraph V; reason: injective relabeling preserves all visited sets, edges and distances; vertices outside the known set are isolated
--   - encoding: GreedyExp1 with arbitrary closest-node and shortest-path choices → every observation-only policy satisfying IsGreedyAlgorithm; reason: the predicate specifies exactly Algorithm 1 decisions and no success property; every tie resolution along a run is represented by such a history policy
--   - encoding: finite potential changes with vertex charge in the integers and edge charge in the naturals → extended-natural distances, integer vertex differences and natural edge differences evaluated at first arrivals and eliminations; reason: the common spanning tree makes each relevant potential finite; integer subtraction retains the last vertex charge -1; never-occurring events receive zero without assuming termination
--   - encoding: edges eliminated one at a time in an arbitrary fixed order → a universally quantified injective edge ranking at each move; reason: every order on the finite eliminated set extends to such a ranking; unused rankings have no effect
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), Lemma 2, p.7 (PDF p.8)

import Definitions.Def_IntervalExplore_KT1_Charges

set_option autoImplicit false

namespace IntervalExplore.KT1

/-- Lemma 2, p.7 (PDF p.8); vertex charges, including -1, are summed in ℤ. -/
theorem lemma_2 {V : Type} [Fintype V] [DecidableEq V] (W : World V)
    (A : Alg) (hA : IsGreedyAlgorithm A)
    (hn : 3 ≤ Fintype.card V) (hm : Fintype.card V ≤ edgeCount W.graph)
    (htree : CommonTree W.dynamic) (order : EliminationOrder V) :
    ∃ t : ℕ, (t : ℤ) ≤ (Fintype.card V : ℤ) + totalVertexCharge W A +
      (totalEdgeCharge W A order : ℤ) ∧
      worldKnown W A t = worldVisited W A t := by sorry

end IntervalExplore.KT1
