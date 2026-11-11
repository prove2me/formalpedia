-- Prove2me | Theorems.Thm_IntervalExplore_KT1_corollary_3
-- name    : IntervalExplore.KT1.corollary_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:52.163297+00:00
-- url     : https://prove2.me/theorems/51dabe49-a12e-43ae-9d43-7bf0c9abc0bc
-- title:
--   Corollary 3 — large-threshold edge-charge tail
-- statement:
--   Let $G=(V,E)$ be a finite simple undirected graph with $n=|V|\ge3$ and $m=|E|\ge n$, and let every snapshot contain one common spanning tree. Fix any injective identifiers, fixed local port numbering and starting vertex, and any run of GreedyExp1, including every resolution of its closest-node and shortest-path choices.
--   Choose any edge-elimination order and let $F'(j)=|\{e\in E:\iota_E(e)\ge j\}|$. For every integer $k\ge2\ln n$,
--   $$
--   F'(2k-1)\le \frac{n\ln n}{k}+1.
--   $$
--   The threshold uses the natural logarithm. Since $n\ge3$, every admissible integer $k$ is positive. This estimate controls the large-charge regime with the precise coefficient in the source.
--
--   Differences from the source:
--   - encoding: vertices with unique identifiers and their exploration map → a finite carrier V, injective natural-number labels, an observation map on labels and its pullback to SimpleGraph V; reason: injective relabeling preserves all visited sets, edges and distances; vertices outside the known set are isolated
--   - encoding: GreedyExp1 with arbitrary closest-node and shortest-path choices → every observation-only policy satisfying IsGreedyAlgorithm; reason: the predicate specifies exactly Algorithm 1 decisions and no success property; every tie resolution along a run is represented by such a history policy
--   - encoding: finite potential changes with vertex charge in the integers and edge charge in the naturals → extended-natural distances, integer vertex differences and natural edge differences evaluated at first arrivals and eliminations; reason: the common spanning tree makes each relevant potential finite; integer subtraction retains the last vertex charge -1; never-occurring events receive zero without assuming termination
--   - encoding: edges eliminated one at a time in an arbitrary fixed order → a universally quantified injective edge ranking at each move; reason: every order on the finite eliminated set extends to such a ranking; unused rankings have no effect
--   - encoding: an integer k≥2 ln n → a natural number k with the real inequality 2*Real.log n≤k; reason: n≥3 makes every admissible integer positive, so the domains coincide
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), Corollary 3, p.9 (PDF p.10)

import Definitions.Def_IntervalExplore_KT1_Charges

set_option autoImplicit false

namespace IntervalExplore.KT1

/-- Corollary 3, p.9 (PDF p.10). Its integer threshold is positive since n ≥ 3. -/
theorem corollary_3 {V : Type} [Fintype V] [DecidableEq V] (W : World V)
    (A : Alg) (hA : IsGreedyAlgorithm A)
    (hn : 3 ≤ Fintype.card V) (hm : Fintype.card V ≤ edgeCount W.graph)
    (htree : CommonTree W.dynamic) (order : EliminationOrder V) (k : ℕ)
    (hk : 2 * Real.log (Fintype.card V) ≤ (k : ℝ)) :
    (Fprime W A order (2 * k - 1) : ℝ) ≤
      (Fintype.card V : ℝ) * Real.log (Fintype.card V) / k + 1 := by sorry

end IntervalExplore.KT1
