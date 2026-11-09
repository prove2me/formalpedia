-- Prove2me | Theorems.Thm_MetricTSPSublinear_corollary_5_4
-- name    : MetricTSPSublinear.corollary_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:28:15.367464+00:00
-- url     : https://prove2.me/theorems/fe6214fb-ccd8-4011-90a9-7e887abda558
-- title:
--   Corollary 5.4 — $K(S)\le K$
-- statement:
--   Let $d$ be a metric on $V$. For every vertex set $S\subseteq V$,
--   $$K(S)\le K,$$
--   where $K(S)$ is the cut LP value of the metric induced on $S$ and $K=K(V)$.
--
--   The refinement loop of the algorithm grows $S$ while $K(S)$ increases; this bound caps the number of rounds.
--
--   Differences from the source:
--   - encoding: an n-point metric (V, d) → DoublingMST.IsMetric d on Fin n: d u v = 0 iff u = v, symmetry, triangle inequality; reason: same instances; nonnegativity follows
--   - encoding: K(S), K → cutLP d S, cutLP d Finset.univ; reason: the LP optima for a metric
--   - encoding: a vertex set S ⊆ V → every S ⊆ Fin n, including ∅; reason: K(∅) = 0 ≤ K
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §5.3, Corollary 5.4, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_cutLP

namespace MetricTSPSublinear

/-- **Corollary 5.4.** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §5.3, p.18 (PDF p.20): "Given a vertex set S ⊆ V, it holds that K(S) ≤ K."

For every metric `d` on `Fin n` and every point set `S`: `cutLP d S ≤ cutLP d Finset.univ`. -/
theorem corollary_5_4 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (S : Finset (Fin n)) :
    cutLP d S ≤ cutLP d Finset.univ := by sorry

end MetricTSPSublinear
