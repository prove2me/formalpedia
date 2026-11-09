-- Prove2me | Theorems.Thm_MetricTSPSublinear_lemma_4_4
-- name    : MetricTSPSublinear.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:30:46.290587+00:00
-- url     : https://prove2.me/theorems/9070c7f0-5a99-4b0b-80b9-c3c42fbd30ac
-- title:
--   Lemma 4.4 — $w(T\langle S\rangle)-2D\le K(S)\le w(T\langle S\rangle)$
-- statement:
--   Let $d$ be a metric, $T$ a minimum spanning tree, $D=M-K$, and for $S\subseteq V$ let $K(S)$ be the cut LP value of the metric induced on $S$ and $T\langle S\rangle$ the minimal subtree of $T$ spanning $S$. Then
--   $$w(T\langle S\rangle)-2D\ \le\ K(S)\ \le\ w(T\langle S\rangle).$$
--
--   The algorithm estimates $K$ through $K(S)$ for a growing terminal set $S$; this lemma ties $K(S)$ to the MST.
--
--   Differences from the source:
--   - generalization: T, the MST (unique after tie-breaking by edge IDs, p.10) → every minimum spanning tree E; reason: the page's T is one of them; the proof uses only minimality
--   - encoding: an n-point metric (V, d) → DoublingMST.IsMetric d on Fin n: d u v = 0 iff u = v, symmetry, triangle inequality; reason: same instances; nonnegativity follows
--   - encoding: M = w(T), the MST weight → DoublingMST.mstWeight d, the infimum of the edge-weight sum over spanning trees of the complete graph on Fin n, with edge weight min(d u v, d v u); reason: equals the MST weight for a metric
--   - encoding: K, the optimal value of the Cut LP (P) → cutLP d Finset.univ, the infimum of the objective of (P) over its feasible points; reason: the LP's optimum for a metric
--   - encoding: K(S), the Cut LP on the metric induced by S; T⟨S⟩ → cutLP d S; hull E S with weight DoublingMST.treeWeight d (hull E S); reason: the same quantities
--   - encoding: a vertex set S → every S ⊆ Fin n, including |S| ≤ 1; reason: there K(S) = w(T⟨S⟩) = 0 and the claim holds since D ≥ 0
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §4.2, Lemma 4.4, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_cutLP
import Definitions.Def_MetricTSPSublinear_hull
import Definitions.Def_DoublingMST_mstWeight
import Definitions.Def_DoublingMST_IsMSTOf
import Definitions.Def_DoublingMST_treeWeight

namespace MetricTSPSublinear

/-- **Lemma 4.4.** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §4.2, p.14 (PDF p.16): "It holds that w(T⟨S⟩) − 2D ≤ K(S) ≤ w(T⟨S⟩)."

For every metric `d` on `Fin n`, every minimum spanning tree `E` and every point set `S`: with `T⟨S⟩ = hull E S`
the minimal subtree of `E` spanning `S`, `K(S) = cutLP d S`, and `D = M − K`,
`w(T⟨S⟩) − 2D ≤ K(S) ≤ w(T⟨S⟩)`.

**Formalization Note.** The statement is for every MST `E` and every `S`, including `|S| ≤ 1`, where both sides
of the upper bound are `0`. -/
theorem lemma_4_4 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (E : Finset (Sym2 (Fin n)))
    (hE : DoublingMST.IsMSTOf d Finset.univ E) (S : Finset (Fin n)) :
    DoublingMST.treeWeight d (hull E S) - 2 * (DoublingMST.mstWeight d - cutLP d Finset.univ) ≤ cutLP d S ∧
      cutLP d S ≤ DoublingMST.treeWeight d (hull E S) := by sorry

end MetricTSPSublinear
