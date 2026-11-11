-- Prove2me | Theorems.Thm_IntervalExplore_KT1_lemma_5
-- name    : IntervalExplore.KT1.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:00.502545+00:00
-- url     : https://prove2.me/theorems/5fa51cd2-d67a-4362-8557-a7c618c5f189
-- title:
--   Lemma 5 — edge-charge tail bound
-- statement:
--   Let $G=(V,E)$ be a finite simple undirected graph with $n=|V|\ge3$ and $m=|E|\ge n$, and let every snapshot contain one common spanning tree. Fix any injective identifiers, fixed local port numbering and starting vertex, and any run of GreedyExp1, including every resolution of its closest-node and shortest-path choices.
--   Choose any edge-elimination order and write $F'(j)=|\{e\in E:\iota_E(e)\ge j\}|$. For every positive integer $k$,
--   $$
--   F'(2k-1)\le\frac12 n^{1+1/k}-\frac n2+1.
--   $$
--   This is the exact tail estimate in the source, including its additive constant and subtractive term. It applies to all allowed tie and elimination choices.
--
--   Differences from the source:
--   - encoding: vertices with unique identifiers and their exploration map → a finite carrier V, injective natural-number labels, an observation map on labels and its pullback to SimpleGraph V; reason: injective relabeling preserves all visited sets, edges and distances; vertices outside the known set are isolated
--   - encoding: GreedyExp1 with arbitrary closest-node and shortest-path choices → every observation-only policy satisfying IsGreedyAlgorithm; reason: the predicate specifies exactly Algorithm 1 decisions and no success property; every tie resolution along a run is represented by such a history policy
--   - encoding: finite potential changes with vertex charge in the integers and edge charge in the naturals → extended-natural distances, integer vertex differences and natural edge differences evaluated at first arrivals and eliminations; reason: the common spanning tree makes each relevant potential finite; integer subtraction retains the last vertex charge -1; never-occurring events receive zero without assuming termination
--   - encoding: edges eliminated one at a time in an arbitrary fixed order → a universally quantified injective edge ranking at each move; reason: every order on the finite eliminated set extends to such a ranking; unused rankings have no effect
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), Lemma 5, p.8 (PDF p.9)

import Definitions.Def_IntervalExplore_KT1_Charges

set_option autoImplicit false

namespace IntervalExplore.KT1

/-- Lemma 5, p.8 (PDF p.9), for every tie resolution and elimination order. -/
theorem lemma_5 {V : Type} [Fintype V] [DecidableEq V] (W : World V)
    (A : Alg) (hA : IsGreedyAlgorithm A)
    (hn : 3 ≤ Fintype.card V) (hm : Fintype.card V ≤ edgeCount W.graph)
    (htree : CommonTree W.dynamic) (order : EliminationOrder V) (k : ℕ) (hk : 1 ≤ k) :
    (Fprime W A order (2 * k - 1) : ℝ) ≤
      (1 / 2 : ℝ) * (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) -
        (Fintype.card V : ℝ) / 2 + 1 := by sorry

end IntervalExplore.KT1
