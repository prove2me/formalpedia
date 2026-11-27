-- Prove2me | Theorems.Thm_MetricTSPSublinear_claim_7_1_domination
-- name    : MetricTSPSublinear.claim_7_1_domination
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:07:52.789796+00:00
-- url     : https://prove2.me/theorems/d16f2e05-75de-4558-9dd6-dec95ffb1c0e
-- title:
--   Claim 7.1 (joined fragment shortenings are dominated)
-- statement:
--   This is the domination part of Claim 7.1: joining shortened MST fragments at a common root and shortening them along a half-integral vertex cover of the conflict graph yields distances dominated by the metric.
--
--   Let $d$ be a symmetric distance function on $V$ and $\sigma>0$ the discretization scale. The vertices are partitioned into fragments; every vertex $u$ has a list of edge segments $e_1(u),e_2(u),\dots,e_{h_u}(u)$, where $e_i(u)$ is the $i$-th segment of length $\sigma$ on the path from $u$ up to the root of its fragment (segments may be shared by several vertices of the same fragment). Two segments $e_i(u)$ and $e_j(v)$ of different fragments are in **conflict** if
--   $$(i+j)\,\sigma>d(u,v).$$
--   Let $y$ assign to every segment a value in $\{0,\tfrac12,1\}$ such that $y(e)+y(f)\ge 1$ for every conflicting pair $(e,f)$, and assume the outside constraint $h_u\sigma\le d(u,v)$ whenever $u$ and $v$ lie in different fragments. Shortening every segment $e$ to length $\sigma(1-y(e))$ and joining all fragments at a common root gives the tree distance
--   $$d_{t}(u,v)=\sigma\sum_{i=1}^{h_u}\bigl(1-y(e_i(u))\bigr)+\sigma\sum_{j=1}^{h_v}\bigl(1-y(e_j(v))\bigr)$$
--   for $u,v$ in different fragments. The claim is that
--   $$d_t(u,v)\le d(u,v)\qquad\text{whenever $u$ and $v$ lie in different fragments.}$$
--
--   In the paper this is the key step showing that the local solution $t_P$ of a contracted cell is a feasible dual solution, so that its weight $A_P-\tau_P$ can be counted in the lower bound $L\le K$.
--
--   **Formalization Note** Segment positions are $0$-indexed in Lean, so position $i$ is the $(i+1)$-st segment. The paper first makes the cover monotone along root paths; the inequality holds for every half-integral cover, so monotonicity is not assumed.
-- source:
--   Azarmehr–Behnezhad 2026, Metric TSP in Sublinear Time: Breaking Two Approximation, https://arxiv.org/abs/2611.04283, §7.1.2–7.1.3, pp.23–24 (PDF pp.25–26): constraints (10), conflict rule (11), Claim 7.1 and its proof.

import Mathlib

namespace MetricTSPSublinear

/-- **Claim 7.1 (domination of the joined fragment shortenings).** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time:
Breaking Two Approximation*, arXiv:2611.04283, §7.1.3, p.23–24 (PDF p.25–26): conflict rule (11) "(i + j)σ > d(u, v)",
the half-integral cover `y_e ∈ {0, 1/2, 1}`, and in the proof of Claim 7.1: "after applying the cover, the distances
between fragments are dominated by the metric", using the outside-vertex constraint of (10).

`path u` lists the segments on the path from `u` up to its fragment root (position `i` is the `(i+1)`-st segment
above `u`); `frag u` is the fragment of `u`; `y` is a half-integral cover of all conflicts (11) between segments of
different fragments; `hout` is the outside constraint `d_{t_F}(u, o_F) ≤ d(u, x)` of (10) for the discretized
height. Then after shortening each segment by `σ y_e` and joining all fragments at one root, the tree distance
`d_{t_P}(u, v) = σ Σ (1 − y)` (along `u`'s path) `+ σ Σ (1 − y)` (along `v`'s path) is at most `d(u, v)`.

**Formalization Note.** The paper first makes the cover monotone along root paths; the inequality holds for any
half-integral cover, so no monotonicity is assumed. Segments may be shared between paths (the fragments are trees). -/
theorem claim_7_1_domination {n : ℕ} (d : Fin n → Fin n → ℝ) {ι Seg : Type} (σ : ℝ) (hσ : 0 < σ)
    (frag : Fin n → ι) (path : Fin n → List Seg) (y : Seg → ℝ)
    (hsymm : ∀ u v, d u v = d v u) (hy : ∀ e, y e = 0 ∨ y e = 1 / 2 ∨ y e = 1)
    (hcover : ∀ u v, frag u ≠ frag v → ∀ (i : Fin (path u).length) (j : Fin (path v).length),
      d u v < ((i : ℝ) + 1 + ((j : ℝ) + 1)) * σ → 1 ≤ y ((path u).get i) + y ((path v).get j))
    (hout : ∀ u v, frag u ≠ frag v → ((path u).length : ℝ) * σ ≤ d u v) :
    ∀ u v, frag u ≠ frag v →
      σ * ((path u).map (fun e => 1 - y e)).sum + σ * ((path v).map (fun e => 1 - y e)).sum ≤ d u v := by sorry

end MetricTSPSublinear
