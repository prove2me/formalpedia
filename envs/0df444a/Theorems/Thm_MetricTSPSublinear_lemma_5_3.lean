-- Prove2me | Theorems.Thm_MetricTSPSublinear_lemma_5_3
-- name    : MetricTSPSublinear.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:30:47.087731+00:00
-- url     : https://prove2.me/theorems/40f4bbab-7625-417d-b3b4-41d0548fd9f6
-- title:
--   Lemma 5.3 — a non-expansive map $q:V\to R(C)$ fixing $S$, determined by the distances to $S$
-- statement:
--   Let $d$ be a metric on $V$, $S\subseteq V$ and $C$ a weighted Steiner tree on $S$ dominated by the metric. There is a map $q:V\to R(C)$, where $q_v$ depends on $v$ only through the distances $(d(v,s))_{s\in S}$, such that
--   $$q_s=s\quad(s\in S)\qquad\text{and}\qquad d_C(q_u,q_v)\le d(u,v)\quad(u,v\in V).$$
--
--   The map places every vertex on the computed core; the cell decomposition of the core then decomposes the whole metric.
--
--   Differences from the source:
--   - reading: the distances d(v, s), v ∈ V, s ∈ S, suffice to compute a map q → q_v = Φ((d(v, s))_{s∈S}) for some function Φ of the distance vector; reason: the claim is that q_v is determined by these distances; the machine-level cost of computing it belongs to Lemma 9.1
--   - encoding: an n-point metric (V, d) → DoublingMST.IsMetric d on Fin n: d u v = 0 iff u = v, symmetry, triangle inequality; reason: same instances; nonnegativity follows
--   - encoding: a dominated tree C spanning S, R(C), d_C → SteinerTree S with Dominated d C; RPoint C.T.G with rdist C.T; s as a point of R(C) is its node ι s; reason: the same objects
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §5.3, Lemma 5.3, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_Dominated
import Definitions.Def_MetricTSPSublinear_rdist

namespace MetricTSPSublinear

/-- **Lemma 5.3.** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §5.3, p.17 (PDF p.19): "For any dominated tree C spanning S, the distances d(v, s), for
v ∈ V and s ∈ S, suffice to compute a map q : V → R(C) satisfying q_s = s (s ∈ S) and d_C(q_u, q_v) ≤ d(u, v)
(u, v ∈ V)."

For every metric `d` on `Fin n`, every point set `S` and every Steiner tree `C` on `S` dominated by `d`, there is a
function `Φ` from vectors `(r_s)_{s ∈ S}` to points of `R(C)` such that `q_v := Φ((d(v, s))_{s ∈ S})` satisfies
`q_s = ι(s)` for every `s ∈ S` and `d_{R(C)}(q_u, q_v) ≤ d(u, v)` for all `u, v`.

**Formalization Note.** "The distances d(v, s) … suffice to compute a map q" is the factorization of `q` through the
vector of distances from `v` to `S`: `q_v` depends on `v` only through that vector. The terminal `s` as a point of
`R(C)` is its node `ι s`. -/
theorem lemma_5_3 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (S : Finset (Fin n)) (C : SteinerTree S)
    (hC : Dominated d C) :
    ∃ Φ : ({s // s ∈ S} → ℝ) → RPoint C.T.G,
      (∀ s ∈ S, Φ (fun t => d s t) = RPoint.vtx (C.ι s)) ∧
      ∀ u v, rdist C.T (Φ (fun t => d u t)) (Φ (fun t => d v t)) ≤ d u v := by sorry

end MetricTSPSublinear
