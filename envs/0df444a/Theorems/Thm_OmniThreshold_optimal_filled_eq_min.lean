-- Prove2me | Theorems.Thm_OmniThreshold_optimal_filled_eq_min
-- name    : OmniThreshold.optimal_filled_eq_min
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:34:46.566143+00:00
-- url     : https://prove2.me/theorems/79a750d7-18be-451d-b5e2-7398c1751745
-- title:
--   Proof of Theorem 2, p.9 — at an optimum, orders are cancelled only when no inventory is left
-- statement:
--   Let $p\ge0$, $s_{ji}\ge0$ and $s_{ji}<c_i$ for all locations $i,j$. Let $A^O\le\mathcal D^O$ coordinatewise, and write $L=\sum_i(\mathcal I_i-\min(\mathcal I_i,\mathcal D_i^P))$ for the inventory left after in-store demand. Then every optimal solution $(C,R,F)$ of LP (1) fills
--   $$
--   \sum_{i,j}F_{ij}=\min\Bigl(\sum_iA_i^O,\ L\Bigr)
--   $$
--   online orders. In particular, if $\sum_iA_i^O=\min(S,\sum_i\mathcal D_i^O)$, as under the Global Threshold $S$, then
--   $$
--   \sum_{i,j}F_{ij}=\min\Bigl(S,\ \sum_{i=1}^n\mathcal D_i^O,\ \sum_{i=1}^n\bigl(\mathcal I_i-\min(\mathcal I_i,\mathcal D_i^P)\bigr)\Bigr).
--   $$
--   This is the first step of the proof of Theorem 2: since cancelling is costlier than shipping, accepted orders are cancelled only when no inventory is left.
--
--   **Formalization Note** An optimal solution is a feasible point whose LP (1) objective is at most that of every feasible point.
--
--   Differences from the source:
--   - generalization: a single cancellation cost $c>\max\{s_{ji}\}$ → per-location costs with $s_{ji}<c_i$ for all $i,j$; reason: LP (1) is written with per-location $c_i$, and the paper's assumption is the case $c_i=c$
--   - reading: penalty and shipping costs (no sign stated) → $p\ge0$ and $s_{ji}\ge0$; reason: they are costs in the model of §1.1
--   - generalization: the Global Threshold's accepted orders → any accepted vector $A^O\le\mathcal D^O$, with the threshold case as the second clause; reason: the threshold's $A^O$ satisfies $A^O\le\mathcal D^O$ and $\sum_iA_i^O=\min(S,\sum_i\mathcal D_i^O)$, so the second clause is the printed identity
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, proof of Theorem 2, p.9, "Consequently, ∑ F = min(S, ∑ D^O, ∑ (I − min(I, D^P)))"; cost assumption p.4

import Mathlib
import Definitions.Def_OmniThreshold_IsFeasible
import Definitions.Def_OmniThreshold_lp1Objective

namespace OmniThreshold

/-- **Proof of Theorem 2, p.9: accepted orders are cancelled only when no inventory is left**
(Jia, Karp, Ravi & Tayur, *Effective Online Order Acceptance Policies for Omni-Channel
Fulfillment*, SSRN 3932692, proof of Theorem 2, p.9: "in the optimal solution accepted orders will
be cancelled only if there is no available inventory to fulfill the orders. Consequently,
`∑_{i,j} F_ij = min(S, ∑_i D_i^O, ∑_i (I_i − min(I_i, D_i^P)))`").

Under the model's cost assumptions (`p ≥ 0`, `s_ji ≥ 0`, and `s_ji < c_i`, p.4), every optimal
solution `x = (C, R, F)` of LP (1) with accepted orders `A ≤ D^O` fills
`∑_{i,j} F_ij = min(∑_i A_i, ∑_i (I_i − min(I_i, D_i^P)))` orders; in particular, when
`∑_i A_i = min(S, ∑_i D_i^O)` (the Global Threshold `S`), `∑_{i,j} F_ij` is the three-term minimum
of the paper.

**Formalization Note** "Optimal solution" is a feasible `x` whose LP (1) objective is at most that
of every feasible `y`. The paper's single cancellation cost `c > max{s_ji}` (p.4) is generalized to
per-location `c_i > s_ji`. -/
theorem optimal_filled_eq_min {n : ℕ} (I : Fin n → ℕ) (p : ℝ) (c : Fin n → ℝ)
    (s : Fin n → Fin n → ℝ) (hp : 0 ≤ p) (hs : ∀ i j, 0 ≤ s j i) (hsc : ∀ i j, s j i < c i)
    (DP DO A : Fin n → ℕ) (hA : ∀ i, A i ≤ DO i)
    (x : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (hx : IsFeasible I DP A x)
    (hopt : ∀ y, IsFeasible I DP A y →
      lp1Objective p c s I DP DO A x ≤ lp1Objective p c s I DP DO A y) :
    (∑ i, ∑ j, x.2.2 i j =
        min (∑ i, (A i : ℝ)) (∑ i, ((I i : ℝ) - min (I i : ℝ) (DP i : ℝ)))) ∧
    ∀ S : ℕ, ∑ i, A i = min S (∑ i, DO i) →
      ∑ i, ∑ j, x.2.2 i j =
        min (min (S : ℝ) (∑ i, (DO i : ℝ))) (∑ i, ((I i : ℝ) - min (I i : ℝ) (DP i : ℝ))) := by sorry

end OmniThreshold
