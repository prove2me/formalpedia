-- Prove2me | Theorems.Thm_IntervalExplore_KT1_lemma_6
-- name    : IntervalExplore.KT1.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:07.754264+00:00
-- url     : https://prove2.me/theorems/ad07cafe-b085-4abd-996e-b417179c7828
-- title:
--   Lemma 6 — total edge charge with one universal constant
-- statement:
--   There is a real constant $C>0$, independent of every instance, with the following property. Let $G=(V,E)$ be a finite simple undirected graph with $n=|V|\ge3$ and $m=|E|\ge n$, and let every snapshot contain one common spanning tree. Fix any injective identifiers, fixed local port numbering and starting vertex, and any run of GreedyExp1, including every resolution of its closest-node and shortest-path choices.
--   For every per-move edge-elimination order,
--   $$
--   \sum_{e\in E}\iota_E(e)\le C\bigl(\xi(n,m)m+n(\log_2 n)^2\bigr),\qquad
--   \xi(n,m)=\frac{\ln n}{1+\ln m-\ln n}.
--   $$
--   The paper writes $O(\xi m+n\log^2 n)$; its proof on p.9 yields a universal constant $C$. No numerical value is selected because the proof leaves this constant universal. The same $C$ works across all sizes, graphs, schedules, identifiers, port numberings, starting vertices, tie resolutions and elimination orders. This is the edge part of the exploration-time estimate.
--
--   Differences from the source:
--   - encoding: vertices with unique identifiers and their exploration map → a finite carrier V, injective natural-number labels, an observation map on labels and its pullback to SimpleGraph V; reason: injective relabeling preserves all visited sets, edges and distances; vertices outside the known set are isolated
--   - encoding: GreedyExp1 with arbitrary closest-node and shortest-path choices → every observation-only policy satisfying IsGreedyAlgorithm; reason: the predicate specifies exactly Algorithm 1 decisions and no success property; every tie resolution along a run is represented by such a history policy
--   - encoding: finite potential changes with vertex charge in the integers and edge charge in the naturals → extended-natural distances, integer vertex differences and natural edge differences evaluated at first arrivals and eliminations; reason: the common spanning tree makes each relevant potential finite; integer subtraction retains the last vertex charge -1; never-occurring events receive zero without assuming termination
--   - encoding: edges eliminated one at a time in an arbitrary fixed order → a universally quantified injective edge ranking at each move; reason: every order on the finite eliminated set extends to such a ranking; unused rankings have no effect
--   - encoding: the uniform O(ξm+n log² n) bound → one positive real constant C quantified before every instance, multiplying ξm+n(log₂ n)²; reason: the proof leaves its O-constant universal; the explicit inequality states exactly that uniform bound
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), Lemma 6 and its proof, p.9 (PDF p.10)

import Definitions.Def_IntervalExplore_KT1_Charges
import Definitions.Def_IntervalExplore_KT1_Rates

set_option autoImplicit false

namespace IntervalExplore.KT1

/-- Lemma 6, p.9 (PDF p.10). The paper writes O(·); its proof yields an
absolute C, chosen before every graph, schedule, labeling, port system, run and order. -/
theorem lemma_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (W : World V)
      (A : Alg), IsGreedyAlgorithm A → 3 ≤ Fintype.card V →
      Fintype.card V ≤ edgeCount W.graph → CommonTree W.dynamic →
      ∀ order : EliminationOrder V,
        (totalEdgeCharge W A order : ℝ) ≤ C * chargeScale (Fintype.card V) (edgeCount W.graph) := by sorry

end IntervalExplore.KT1
