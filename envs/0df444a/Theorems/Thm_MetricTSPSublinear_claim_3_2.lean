-- Prove2me | Theorems.Thm_MetricTSPSublinear_claim_3_2
-- name    : MetricTSPSublinear.claim_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:28:47.884141+00:00
-- url     : https://prove2.me/theorems/d285eb1c-d0ad-4cf4-8d0f-d62a5f5690e0
-- title:
--   Claim 3.2 — $M/2\le K\le M$
-- statement:
--   Let $d$ be an $n$-point metric, $M$ the weight of its minimum spanning tree and $K$ the optimal value of the cut LP (P). Then
--   $$\frac M2\le K\le M.$$
--
--   The upper bound says that (P) relaxes the MST problem; the lower bound says that the relaxation loses at most a factor $2$. Together with Claim 3.3 this reduces breaking the factor $2$ for TSP to distinguishing $K\approx M$ from $K\approx M/2$.
--
--   Differences from the source:
--   - encoding: an n-point metric (V, d) → DoublingMST.IsMetric d on Fin n: d u v = 0 iff u = v, symmetry, triangle inequality; reason: same instances; nonnegativity follows
--   - encoding: M = w(T), the MST weight → DoublingMST.mstWeight d, the infimum of the edge-weight sum over spanning trees of the complete graph on Fin n, with edge weight min(d u v, d v u); reason: equals the MST weight for a metric
--   - encoding: K, the optimal value of the Cut LP (P) → cutLP d Finset.univ, the infimum of the objective of (P) over its feasible points; reason: the LP's optimum for a metric
--   - encoding: the n-point metric of the paper (n ≥ 1 implicit) → every n including n = 0; reason: for n ≤ 1 both M and K are 0 and the claim holds
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §3, Claim 3.2, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_cutLP
import Definitions.Def_DoublingMST_mstWeight

namespace MetricTSPSublinear

/-- **Claim 3.2.** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §3, p.10 (PDF p.12): "It holds that M/2 ≤ K ≤ M."

For every `n` and every metric `d` on `Fin n`, with `M = DoublingMST.mstWeight d` the weight of a minimum spanning
tree and `K = cutLP d Finset.univ` the value of the cut LP (P): `M/2 ≤ K ≤ M`.

**Formalization Note.** `n = 0, 1` are included: there `M = K = 0`. -/
theorem claim_3_2 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) :
    DoublingMST.mstWeight d / 2 ≤ cutLP d Finset.univ ∧ cutLP d Finset.univ ≤ DoublingMST.mstWeight d := by sorry

end MetricTSPSublinear
