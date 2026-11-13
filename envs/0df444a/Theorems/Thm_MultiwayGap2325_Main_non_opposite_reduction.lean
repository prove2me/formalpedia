-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_non_opposite_reduction
-- name    : MultiwayGap2325.Main.non_opposite_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-11T04:07:01.253257+00:00
-- url     : https://prove2.me/theorems/0a7c942a-aad5-4fcd-bb86-3b7c83495705
-- title:
--   Lemma 2.2 — Non-opposite reduction
-- statement:
--   Fix $q\ge2$ and $b>0$. Suppose every jointly measurable random non-opposite cut of $\Delta_q$ on any probability space, with any real approximation factor $\alpha$, satisfies $\alpha\ge b$. Then there is a real $g$ such that
--   $$
--   \lim_{k\to\infty}G_k=g\ge b.
--   $$
--   For every $\eta>0$ there is $K\ge2$ such that every integer $k\ge K$ admits an actual finite $k$-terminal instance $I$ with
--   $$
--   \operatorname{gap}(I)\ge b-\eta.
--   $$
--   The cut hypothesis ranges over the full real simplex and arbitrary probability laws. The finite-grid argument in Appendix A is not a restriction of the statement's domain.
--
--   Differences from the source:
--   - encoding: an arbitrary finite undirected graph with distinct terminals → a graph on Fin n with Fin k terminals and an ordered edge list; reason: all finite vertex types admit reindexing; opposite orientations aggregate and loops have zero cost; neither n nor real weights are bounded
--   - encoding: the ratio OPT/LP in the supremum of gaps → OPT/LP when LP is positive and gap 1 when LP=0; reason: LP=0 implies OPT=0 and a positive-LP instance of gap 1 exists for every k≥2; gap_sequence_well_posed states equality of the two suprema
--   - encoding: the limit and eventual finite-instance conclusion → AsymptoticGapAtLeast b with an explicit Tendsto witness; reason: the predicate expands to convergence and the eventual every-k assertion, with K≥2 excluding only irrelevant initial sequence entries
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), Lemma 2.2, p. 4; §5 preamble, p. 11; proof in Appendix A, p. 34

import Definitions.Def_MultiwayGap2325_Main_RandomCuts

namespace MultiwayGap2325.Main

/-- Lemma 2.2, p.4, with the full continuous conclusion of Appendix A. -/
theorem non_opposite_reduction (q : ℕ) (hq : 2 ≤ q) (b : ℝ) (hb : 0 < b)
    (hcuts : ∀ (Ξ : Type) [MeasurableSpace Ξ]
      (P : MeasureTheory.Measure Ξ) [MeasureTheory.IsProbabilityMeasure P]
      (C : RandomNonOppositeCut q Ξ P) (α : ℝ),
      HasApproximationFactor C α → b ≤ α) :
    AsymptoticGapAtLeast b := by sorry

end MultiwayGap2325.Main
