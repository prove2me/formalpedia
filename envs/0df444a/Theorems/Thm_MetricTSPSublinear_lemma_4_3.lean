-- Prove2me | Theorems.Thm_MetricTSPSublinear_lemma_4_3
-- name    : MetricTSPSublinear.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:29:50.195201+00:00
-- url     : https://prove2.me/theorems/514ab91b-2675-436d-a600-5d191bce1760
-- title:
--   Lemma 4.3 — a dominated MST shortening of weight $\ge K-D=M-2D$
-- statement:
--   Let $d$ be a metric, $T$ a minimum spanning tree, $M=w(T)$, $K$ the cut LP value and $D=M-K$. There is a shortening $T_0$ of $T$ (same edges, $0\le w_{T_0}(e)\le w_T(e)$) that is dominated by the metric and satisfies
--   $$w(T_0)\ \ge\ K-D\ =\ M-2D.$$
--
--   When $D$ is small, the MST thus carries a nearly optimal dual solution; this is the comparison object of the paper's analysis.
--
--   Differences from the source:
--   - generalization: T, the MST (unique after tie-breaking by edge IDs, p.10) → every minimum spanning tree E (DoublingMST.IsMSTOf d Finset.univ E); reason: the page's T is one of them; the proof uses only that T is a spanning tree of least weight
--   - encoding: an n-point metric (V, d) → DoublingMST.IsMetric d on Fin n: d u v = 0 iff u = v, symmetry, triangle inequality; reason: same instances; nonnegativity follows
--   - encoding: M = w(T), the MST weight → DoublingMST.mstWeight d, the infimum of the edge-weight sum over spanning trees of the complete graph on Fin n, with edge weight min(d u v, d v u); reason: equals the MST weight for a metric
--   - encoding: K, the optimal value of the Cut LP (P) → cutLP d Finset.univ, the infimum of the objective of (P) over its feasible points; reason: the LP's optimum for a metric
--   - encoding: a shortening T₀ of T → a weight function w' with 0 ≤ w' e ≤ w(e) on E, and w(T₀) = Σ_{e∈E} w' e; reason: a shortening keeps the edges and changes the weights
--   - encoding: K − D = M − 2D → K − (M − K); reason: the same number
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §4.2, Lemma 4.3, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_cutLP
import Definitions.Def_MetricTSPSublinear_IsDominatedShortening
import Definitions.Def_DoublingMST_mstWeight
import Definitions.Def_DoublingMST_IsMSTOf

namespace MetricTSPSublinear

/-- **Lemma 4.3.** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §4.2, p.13 (PDF p.15): "There exists a dominated shortening T0 of T, such that
w(T0) ≥ K − D = M − 2D."

For every metric `d` on `Fin n` and every minimum spanning tree `E` of the complete graph (`DoublingMST.IsMSTOf d
Finset.univ E`), there is a dominated shortening `w'` of `E` with `∑_{e∈E} w'(e) ≥ K − D`, where
`M = DoublingMST.mstWeight d`, `K = cutLP d Finset.univ` and `D = M − K`.

**Formalization Note.** The page's `T` is "the" MST; the statement is for every MST, so no tie-breaking is needed.
`K − D = M − 2D` is an identity. -/
theorem lemma_4_3 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (E : Finset (Sym2 (Fin n)))
    (hE : DoublingMST.IsMSTOf d Finset.univ E) :
    ∃ w' : Sym2 (Fin n) → ℝ, IsDominatedShortening d E w' ∧
      cutLP d Finset.univ - (DoublingMST.mstWeight d - cutLP d Finset.univ) ≤ ∑ e ∈ E, w' e := by sorry

end MetricTSPSublinear
