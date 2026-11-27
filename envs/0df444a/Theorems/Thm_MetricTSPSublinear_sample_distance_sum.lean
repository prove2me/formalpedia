-- Prove2me | Theorems.Thm_MetricTSPSublinear_sample_distance_sum
-- name    : MetricTSPSublinear.sample_distance_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:21:43.625822+00:00
-- url     : https://prove2.me/theorems/3b3541e5-e7d6-544e-accc-a21773c7e099
-- title:
--   $\sum_v d(v,S_0)\le k\cdot\mathrm{cost}(\pi)$ when $S_0$ hits every $k$-window of a tour
-- statement:
--   Let $d$ be a metric on $V=\{0,\dots,n-1\}$, let $\pi$ be a cyclic ordering of $V$ (a tour visiting $\pi(0),\pi(1),\dots,\pi(n-1)$ and returning to $\pi(0)$) of length
--   $$\mathrm{cost}(\pi)=\sum_{i=0}^{n-1} d\bigl(\pi(i),\pi(i+1 \bmod n)\bigr),$$
--   and let $S_0\subseteq V$ be nonempty. Suppose that every window of $k$ consecutive positions of the tour contains a point of $S_0$: for every position $i$ there is $0\le j<k$ with $\pi(i+j \bmod n)\in S_0$. Then
--   $$\sum_{v\in V} d(v,S_0)\le k\cdot \mathrm{cost}(\pi),\qquad\text{where } d(v,S_0)=\min_{s\in S_0}d(v,s).$$
--
--   In the paper this bounds the total $\sum_v d(v,S_{\mathrm{root}})$ of the importance-sampling upper bounds $b_v=d(v,S_{\mathrm{root}})$ used to estimate the contribution $A$ of the contracted cells: taking $\pi$ a shortest tour ($\mathrm{cost}\le 2M$) and $S_0$ a random sample that hits every window of length $\tilde O(n^{a_0})$ gives $\sum_v b_v=\tilde O(n^{a_0}M)$.
--
--   **Formalization Note** Positions advance cyclically via `finRotate n`. Only the deterministic part is stated; the probability that a random sample hits every window is a separate step.
-- source:
--   Azarmehr–Behnezhad 2026, Metric TSP in Sublinear Time: Breaking Two Approximation, https://arxiv.org/abs/2611.04283, §9.2.1, proof of Claim 9.5, p.37 (PDF p.39).

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSP_model

namespace MetricTSPSublinear

/-- **Distances to a sample that hits every window of a tour.** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time:
Breaking Two Approximation*, arXiv:2611.04283, §9.2.1, proof of Claim 9.5, p.37 (PDF p.39): "Divide the Hamiltonian
cycle into subpaths by cutting it at the vertices of Sroot. For a vertex v, we bound d(v, Sroot), by the length of the
subpath that includes it. Since Sroot includes a vertex sample of size n^{1−a0}, with high probability, at least one in
every Õ(n^{a0}) consecutive vertices of the Hamiltonian cycle is in Sroot. Therefore, Σ_v b_v = Σ_v d(v, Sroot) ≤
Õ(n^{a0} M)."

Deterministic core of this estimate: if every window of `k` consecutive positions of the tour `π` (positions
`i, i+1, …, i+k−1` cyclically) contains a point of `S0`, then `Σ_v d(v, S0) ≤ k · cost(π)`.

**Formalization Note.** The tour is an ordering `π` with cost `MetricTSP.tourCost d π` (successor of a position via
`finRotate n`); `d(v, S0)` is `S0.inf' _ (d v ·)`. The probabilistic statement (a random sample hits every window)
and `cost(π) ≤ 2M` for a shortest tour are separate steps. -/
theorem sample_distance_sum {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (π : Equiv.Perm (Fin n)) (S0 : Finset (Fin n)) (hS0 : S0.Nonempty) (k : ℕ)
    (hwin : ∀ i : Fin n, ∃ j < k, π ((finRotate n)^[j] i) ∈ S0) :
    ∑ v, S0.inf' hS0 (fun s => d v s) ≤ k * MetricTSP.tourCost d π := by sorry

end MetricTSPSublinear
