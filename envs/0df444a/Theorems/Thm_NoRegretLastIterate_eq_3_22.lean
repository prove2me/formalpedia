-- Prove2me | Theorems.Thm_NoRegretLastIterate_eq_3_22
-- name    : NoRegretLastIterate.eq_3_22
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T13:31:17.381623+00:00
-- url     : https://prove2.me/theorems/be540c5d-1bb8-4f07-82a7-d9cd09a33496
-- title:
--   Eq. (3.22) — under $Q_t\to q^*$ a.s., $\liminf\frac1t\sum Q_s(1-Q_s)\ge\gamma(q^*)$
-- statement:
--   Let $0<q^*<1$ and let $(Q_t)_{t\ge1}$ be a real-valued random sequence with $Q_t\to q^*$ almost surely. Then almost surely
--   $$
--   \liminf_{t\to\infty}\frac1t\sum_{s=1}^tQ_s(1-Q_s)\ \ge\ \min\Big\{\frac{q^*(2-q^*)}4,\ \frac{(1+q^*)(1-q^*)}4\Big\}=:\gamma(q^*) .
--   $$
--
--   When $Q_s$ is player 2's mixed strategy, $Q_s(1-Q_s)$ is the conditional variance of the martingale difference $J_s-Q_s$, so (3.22) says the sum of conditional variances grows linearly. This is the variance condition for the martingale central limit theorem used in Eq. (3.26).
--
--   **Formalization Note** The $\liminf$ bound is written as: for every $\gamma'<\gamma(q^*)$, eventually $\gamma'\le\frac1t\sum_{s\le t}Q_s(1-Q_s)$.
--
--   Differences from the source:
--   - generalization: Q_t player 2's mixed strategy in the play of Theorem 3.4, q∗ the NE → any real-valued process Q on any measure space and any q∗ ∈ (0, 1); reason: the statement is a pathwise consequence of Q_t → q∗; the play is a special case
--   - encoding: lim inf_t (1/t) Σ Q_s(1 − Q_s) ≥ γ(q∗) → for every γ′ < γ(q∗), eventually γ′ ≤ (1/t) Σ_{s<t} Q_s(1 − Q_s); reason: equivalent; avoids the junk value of a real-valued liminf
--   - encoding: rounds t = 1, 2, …; f_t applied to (J)^{t−1} → Lean rounds n = t − 1 from 0; F n applied to the first n actions; reason: Lean convention; same instances
-- source:
--   Muthukumar, Phade, Sahai, On the Impossibility of Convergence of Mixed Strategies with Optimal No-Regret Learning, arXiv:2012.02125v3, Eq. (3.22), p.18

import Mathlib

open MeasureTheory Filter Topology

namespace NoRegretLastIterate

/-- Muthukumar, Phade, Sahai, arXiv:2012.02125v3, Eq. (3.22), p.18 ("as a direct consequence of
the claim"). If `Q_t → q∗` almost surely, where `0 < q∗ < 1`, then almost surely
`lim inf_{t→∞} (1/t) Σ_{s=1}^t Q_s(1 − Q_s) ≥ min{q∗(2 − q∗)/4, (1 + q∗)(1 − q∗)/4} =: γ(q∗)`.

**Formalization Note** `Q` is any real-valued process (in the paper, player 2's mixed
strategies). The lim inf bound is stated as: for every `γ′ < γ(q∗)`, eventually
`γ′ ≤ (1/t) Σ_{s<t} Q_s(1 − Q_s)`, which is equivalent and avoids Lean's real `liminf` junk
value. Lean rounds `0, …, t − 1` are paper rounds `1, …, t`. -/
theorem eq_3_22 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Q : ℕ → Ω → ℝ) {q : ℝ}
    (hq : 0 < q ∧ q < 1) (hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => Q n ω) atTop (𝓝 q)) :
    ∀ᵐ ω ∂μ, ∀ γ' : ℝ, γ' < min (q * (2 - q) / 4) ((1 + q) * (1 - q) / 4) →
      ∀ᶠ t : ℕ in atTop, γ' ≤ (∑ s ∈ Finset.range t, Q s ω * (1 - Q s ω)) / t := by sorry

end NoRegretLastIterate
