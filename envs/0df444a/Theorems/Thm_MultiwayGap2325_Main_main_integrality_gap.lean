-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_main_integrality_gap
-- name    : MultiwayGap2325.Main.main_integrality_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:06:06.153254+00:00
-- url     : https://prove2.me/theorems/2c2af731-efa7-4241-945a-8b9ef9e35b72
-- title:
--   Theorem 1.1 — Asymptotic CKR integrality gap exceeds 1.2325
-- statement:
--   For each $k\ge2$, let $G_k$ be the supremum of the CKR integrality gap over all finite undirected $k$-terminal graphs with nonnegative real edge weights. Set
--   $$
--   \beta=\frac{159389999561650025}{129321858575204877}.
--   $$
--   There is a real number $g$ satisfying
--   $$
--   \lim_{k\to\infty}G_k=g\ge\beta>1.2325.
--   $$
--   Furthermore, for every real $\eta>0$, there is an integer $K\ge2$ such that every integer $k\ge K$ admits an actual finite $k$-terminal instance whose gap is at least $\beta-\eta$.
--
--   This is the complete headline claim, retaining the exact rational constant, the existence of a limit, and the eventual every-terminal-count finite witnesses. There is no complexity-theoretic conjecture among its hypotheses.
--
--   **Formalization Note** The real sequence computes its entries from the actual labeling and embedding objectives. No flow certificate, optimality data, claimed lower bound, or assumed convergence is a goal hypothesis.
--
--   Differences from the source:
--   - encoding: an arbitrary finite undirected graph with distinct terminals → a graph on Fin n with Fin k terminals and an ordered edge list; reason: all finite vertex types admit reindexing; opposite orientations aggregate and loops have zero cost; neither n nor real weights are bounded
--   - encoding: the minimum integral cost OPT and the optimum LP of (2) → sInf of the actual feasible objective sets, with a separate attainment and boundedness obligation; reason: both sets are nonempty and bounded below for k≥2, and their optima are attained; these facts are conclusions of finite_optima, not assumptions in the goal
--   - encoding: the ratio OPT/LP in the supremum of gaps → OPT/LP when LP is positive and gap 1 when LP=0; reason: LP=0 implies OPT=0 and a positive-LP instance of gap 1 exists for every k≥2; gap_sequence_well_posed states equality of the two suprema
--   - encoding: the limit as k tends to infinity → an existential real g with Tendsto gapSequence atTop (nhds g), setting G_0=G_1=1; reason: this states convergence explicitly; the two initial values do not affect convergence or eventual witnesses
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), Theorem 1.1 and footnote 1, p. 2; proof, p. 31

import Definitions.Def_MultiwayGap2325_Main_FiniteGap

namespace MultiwayGap2325.Main

/-- Theorem 1.1, p.2: exact constant, convergence, and eventual actual finite witnesses. -/
theorem main_integrality_gap :
    ∃ g : ℝ, Filter.Tendsto gapSequence Filter.atTop (nhds g) ∧
      beta ≤ g ∧ (12325 : ℝ) / 10000 < beta ∧
      ∀ η : ℝ, 0 < η → ∃ K : ℕ, 2 ≤ K ∧ ∀ k : ℕ, K ≤ k →
        ∃ n : ℕ, ∃ I : MultiwayCut.Instance (Fin n) k,
          beta - η ≤ instanceGap I := by sorry

end MultiwayGap2325.Main
