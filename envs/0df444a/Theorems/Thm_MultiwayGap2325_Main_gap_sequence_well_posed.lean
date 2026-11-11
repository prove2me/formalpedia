-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_gap_sequence_well_posed
-- name    : MultiwayGap2325.Main.gap_sequence_well_posed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:06:14.313188+00:00
-- url     : https://prove2.me/theorems/c6bce4f2-b8eb-47b2-a99a-5e699df3d360
-- title:
--   Theorem 1.1 footnote 1 — gap supremum, monotonicity and convergence
-- statement:
--   For every $k\ge2$, there is a positive-LP finite $k$-terminal instance of gap 1. The sets of all gaps and of positive-LP ratios are nonempty and bounded above, and their suprema agree. Moreover,
--   $$
--   1\le G_k\le\tfrac32.
--   $$
--   With $G_0=G_1=1$, the sequence is nondecreasing and converges to a real limit. This retains the source's convergence and CKR boundedness obligations as open mathematical claims, rather than assumptions of the headline theorem.
--
--   Differences from the source:
--   - encoding: an arbitrary finite undirected graph with distinct terminals → a graph on Fin n with Fin k terminals and an ordered edge list; reason: all finite vertex types admit reindexing; opposite orientations aggregate and loops have zero cost; neither n nor real weights are bounded
--   - encoding: the ratio OPT/LP in the supremum of gaps → OPT/LP when LP is positive and gap 1 when LP=0; reason: LP=0 implies OPT=0 and a positive-LP instance of gap 1 exists for every k≥2; gap_sequence_well_posed states equality of the two suprema
--   - encoding: G_k for terminal counts k≥2 → a natural-number sequence with G_0=G_1=1; reason: changing or specifying finitely many initial entries does not change the limit or eventual finite-instance assertions
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), Theorem 1.1 footnote 1, p. 2; Appendix A, p. 34

import Definitions.Def_MultiwayGap2325_Main_FiniteGap

namespace MultiwayGap2325.Main

/-- The elementary and CKR prerequisites behind Theorem 1.1's footnote 1 and Appendix A. -/
theorem gap_sequence_well_posed :
    (∀ k : ℕ, 2 ≤ k →
      (∃ n : ℕ, ∃ I : MultiwayCut.Instance (Fin n) k,
        0 < fractionalOpt I ∧ instanceGap I = 1) ∧
      (finiteGapValues k).Nonempty ∧ BddAbove (finiteGapValues k) ∧
      (positiveGapValues k).Nonempty ∧ BddAbove (positiveGapValues k) ∧
      sSup (finiteGapValues k) = sSup (positiveGapValues k) ∧
      1 ≤ gapSequence k ∧ gapSequence k ≤ (3 : ℝ) / 2) ∧
    Monotone gapSequence ∧
    ∃ g : ℝ, Filter.Tendsto gapSequence Filter.atTop (nhds g) := by sorry

end MultiwayGap2325.Main
