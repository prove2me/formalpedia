-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_exists_nonOppositeCut_of_tendsto_gapSequence
-- name    : MultiwayGap2325.Main.exists_nonOppositeCut_of_tendsto_gapSequence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T21:34:25.367118+00:00
-- url     : https://prove2.me/theorems/de8ea1cd-93bc-4f78-ba28-85a5d6ba6eab
-- title:
--   A random non-opposite cut of the q-vertex simplex whose approximation factor is the limit of the integrality gaps
-- statement:
--   Let $q \ge 2$ and let $g$ be the limit of the sequence $G_k$ of integrality gaps (`MultiwayGap2325.Main.gapSequence`: $G_k$ is the supremum over finite $k$-terminal instances of OPT/LP, with the value $1$ when the LP optimum is $0$). Then there is a probability space $(\Xi, P)$ and a jointly measurable random labeling of the simplex $\Delta_q$ by $\{1,\dots,q\} \cup \{*\}$ that is non-opposite for every outcome (each vertex $e_i$ gets label $i$, and every point gets a label in its positive support or $*$) and has approximation factor $g$: $P[C(x) \ne C(y)] \le g\, d(x,y)$ for all $x, y \in \Delta_q$, with $d$ half the $\ell_1$ distance.
--
--   This is the construction in the proof of Lemma 2.2 (Appendix A, pp. 33–34): restrict a near-optimal random $k$-way cut to a random $q$-face, pass to a limit over grids by compactness, and extend measurably. The hypothesis is the existence of the limit $g$ (a convergent sequence), not a numerical value.
-- source:
--   Dimitar Chakarov and Yury Makarychev, *An Integrality-Gap Lower Bound of 1.2325 for Minimum Multiway Cut*, STOC 2027 submission 697 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/697.pdf), p. 33-34, Appendix A, proof of Lemma 2.2.

import Definitions.Def_MultiwayGap2325_Main_RandomCuts

namespace MultiwayGap2325.Main

theorem exists_nonOppositeCut_of_tendsto_gapSequence (q : ℕ) (hq : 2 ≤ q) (g : ℝ)
    (hg : Filter.Tendsto gapSequence Filter.atTop (nhds g)) :
    ∃ (Ξ : Type) (_ : MeasurableSpace Ξ) (P : MeasureTheory.Measure Ξ)
      (_ : MeasureTheory.IsProbabilityMeasure P) (C : RandomNonOppositeCut q Ξ P),
      HasApproximationFactor C g := by sorry

end MultiwayGap2325.Main
