-- Prove2me | Theorems.Thm_IntervalExplore_KT1_lemma_4
-- name    : IntervalExplore.KT1.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:11.886004+00:00
-- url     : https://prove2.me/theorems/e02de503-91e1-4e88-ab5f-7efd881f61aa
-- title:
--   Lemma 4 — total vertex charge
-- statement:
--   Let $G=(V,E)$ be a finite simple undirected graph with $n=|V|\ge3$ and $m=|E|\ge n$, and let every snapshot contain one common spanning tree. Fix any injective identifiers, fixed local port numbering and starting vertex, and any run of GreedyExp1, including every resolution of its closest-node and shortest-path choices.
--   For the first-stage vertex charges,
--   $$
--   \sum_{v\in V}\iota_V(v)\le 2n\log_2 n.
--   $$
--   The sum is signed, so the start contributes zero and the last new vertex contributes $-1$. It bounds the vertex part of the exploration accounting inequality. This sum does not depend on the stage-two deletion order, which remains arbitrary.
--
--   Differences from the source:
--   - encoding: vertices with unique identifiers and their exploration map → a finite carrier V, injective natural-number labels, an observation map on labels and its pullback to SimpleGraph V; reason: injective relabeling preserves all visited sets, edges and distances; vertices outside the known set are isolated
--   - encoding: GreedyExp1 with arbitrary closest-node and shortest-path choices → every observation-only policy satisfying IsGreedyAlgorithm; reason: the predicate specifies exactly Algorithm 1 decisions and no success property; every tie resolution along a run is represented by such a history policy
--   - encoding: finite potential changes with vertex charge in the integers and edge charge in the naturals → extended-natural distances, integer vertex differences and natural edge differences evaluated at first arrivals and eliminations; reason: the common spanning tree makes each relevant potential finite; integer subtraction retains the last vertex charge -1; never-occurring events receive zero without assuming termination
--   - encoding: edges eliminated one at a time in an arbitrary fixed order → a universally quantified injective edge ranking at each move; reason: every order on the finite eliminated set extends to such a ranking; unused rankings have no effect
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), Lemma 4, p.8 (PDF p.9)

import Definitions.Def_IntervalExplore_KT1_Charges

set_option autoImplicit false

namespace IntervalExplore.KT1

/-- Lemma 4, p.8 (PDF p.9). The vertex sum is independent of deletion order. -/
theorem lemma_4 {V : Type} [Fintype V] [DecidableEq V] (W : World V)
    (A : Alg) (hA : IsGreedyAlgorithm A)
    (hn : 3 ≤ Fintype.card V) (hm : Fintype.card V ≤ edgeCount W.graph)
    (htree : CommonTree W.dynamic) (_order : EliminationOrder V) :
    (totalVertexCharge W A : ℝ) ≤ 2 * Fintype.card V * Real.logb 2 (Fintype.card V) := by sorry

end IntervalExplore.KT1
