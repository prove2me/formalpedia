-- Prove2me | Theorems.Thm_OptimalBAI_TrackStop_cumulative_tracking_bound
-- name    : OptimalBAI.TrackStop.cumulative_tracking_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T02:14:42.211988+00:00
-- url     : https://prove2.me/theorems/d150e5a3-04e3-4c67-a878-a81156003743
-- title:
--   Lemma 15 — tracking a cumulated sum of proportions
-- statement:
--   Let $K$ be a positive integer, $\Sigma_K$ the simplex of dimension $K-1$, and $\delta_i$ the vertex of $\Sigma_K$ with a $1$ on coordinate $i$. For a positive integer $n$, let $p(1),\dots,p(n)\in\Sigma_K$ and $P(k)=p(1)+\dots+p(k)$ for $k\le n$. Let $N(0)=0$ and, for $k\in\{0,\dots,n-1\}$,
--   $$I_{k+1}\in\operatorname*{argmax}_{1\le i\le K}\big[P_i(k+1)-N_i(k)\big],\qquad N(k+1)=N(k)+\delta_{I_{k+1}}.$$
--   Then
--   $$\max_{1\le i\le K}\big|N_i(n)-P_i(n)\big|\le K-1.$$
--
--   The lemma is the deterministic core of C-Tracking: greedily drawing the arm whose count lags most behind the cumulated targets keeps every count within $K-1$ of its target.
--
--   **Formalization Note** Arms are indexed $0,\dots,K-1$; the sequence $p$ keeps the paper's indices $1,\dots,n$, and its other values are ignored.
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 20, Lemma 15

import Mathlib
import Definitions.Def_OptimalBAI_TrackStop_OptimalProportions

namespace OptimalBAI.TrackStop

/-- Lemma 15 (Garivier–Kaufmann, arXiv:1602.04589v2, p. 20). Proportions `p(1), …, p(n) ∈ Σ_K`
with cumulated sums `P(k) = p(1) + ⋯ + p(k)`; `N(0) = 0`, `I_{k+1}` maximizes
`P_i(k+1) - N_i(k)` over `i`, and `N(k+1) = N(k) + δ_{I_{k+1}}`. Then
`max_i |N_i(n) - P_i(n)| ≤ K - 1`. Arms are `Fin K` (the paper's arm `i` is index `i - 1`); the
sequence `p` keeps the paper's 1-based index, and its values outside `1, …, n` are ignored. -/
theorem cumulative_tracking_bound {K : ℕ} (hK : 0 < K) (n : ℕ) (hn : 0 < n)
    (p : ℕ → Fin K → ℝ) (hp : ∀ k, 1 ≤ k → k ≤ n → p k ∈ simplex K)
    (N : ℕ → Fin K → ℝ) (I : ℕ → Fin K)
    (hN0 : N 0 = 0)
    (hI : ∀ k, k < n → ∀ i : Fin K,
      (∑ j ∈ Finset.Icc 1 (k + 1), p j i) - N k i ≤
        (∑ j ∈ Finset.Icc 1 (k + 1), p j (I (k + 1))) - N k (I (k + 1)))
    (hN : ∀ k, k < n → N (k + 1) = N k + Pi.single (I (k + 1)) (1 : ℝ)) :
    ∀ i : Fin K, |N n i - ∑ j ∈ Finset.Icc 1 n, p j i| ≤ (K : ℝ) - 1 := by sorry

end OptimalBAI.TrackStop
