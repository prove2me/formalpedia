-- Prove2me | Theorems.Thm_MetricTSPSublinear_claim_3_3
-- name    : MetricTSPSublinear.claim_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:28:22.106828+00:00
-- url     : https://prove2.me/theorems/f433094b-62a7-47d4-bb2c-7f8a19bef339
-- title:
--   Claim 3.3 — $\max(M,2K)\le \mathrm{TSP}\le M+K$
-- statement:
--   Let $d$ be an $n$-point metric, $M$ its MST weight, $K$ the optimal value of the cut LP (P) and $\mathrm{TSP}$ the length of a shortest Hamiltonian cycle. Then
--   $$\max(M,2K)\ \le\ \mathrm{TSP}\ \le\ M+K.$$
--
--   This sandwich is the bridge between the cut LP and TSP: if $K\le(1-\varepsilon)M$ then $\mathrm{TSP}\le(2-\varepsilon)M$, while if $K$ is close to $M$ then $\mathrm{TSP}$ is close to $2M$.
--
--   Differences from the source:
--   - encoding: an n-point metric (V, d) → DoublingMST.IsMetric d on Fin n: d u v = 0 iff u = v, symmetry, triangle inequality; reason: same instances; nonnegativity follows
--   - encoding: M = w(T), the MST weight → DoublingMST.mstWeight d, the infimum of the edge-weight sum over spanning trees of the complete graph on Fin n, with edge weight min(d u v, d v u); reason: equals the MST weight for a metric
--   - encoding: K, the optimal value of the Cut LP (P) → cutLP d Finset.univ, the infimum of the objective of (P) over its feasible points; reason: the LP's optimum for a metric
--   - encoding: TSP, the length of a shortest Hamiltonian cycle → MetricTSP.tspOpt d, the least cost of a cyclic ordering of all points; 0 for n ≤ 1 and 2d(0,1) for n = 2; reason: for n ≥ 3 the same value; for n ≤ 2 the conventional tour values, with which the claim holds
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §3, Claim 3.3, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_cutLP
import Definitions.Def_DoublingMST_mstWeight

namespace MetricTSPSublinear

/-- **Claim 3.3.** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §3, p.11 (PDF p.13): "It holds that max(M, 2K) ≤ TSP ≤ M + K."

For every `n` and every metric `d` on `Fin n`, with `M = DoublingMST.mstWeight d`, `K = cutLP d Finset.univ` and
`TSP = MetricTSP.tspOpt d` (the least cost of a tour through all points): `max(M, 2K) ≤ TSP ≤ M + K`.

**Formalization Note.** For `n ≤ 2` the tour degenerates: `tspOpt` is `0` for `n ≤ 1` and `2 d(0, 1)` for `n = 2`
(the tour goes to the other point and back); the claim holds there with these values. -/
theorem claim_3_3 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) :
    max (DoublingMST.mstWeight d) (2 * cutLP d Finset.univ) ≤ MetricTSP.tspOpt d ∧
      MetricTSP.tspOpt d ≤ DoublingMST.mstWeight d + cutLP d Finset.univ := by sorry

end MetricTSPSublinear
