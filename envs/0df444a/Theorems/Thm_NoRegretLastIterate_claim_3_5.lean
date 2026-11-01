-- Prove2me | Theorems.Thm_NoRegretLastIterate_claim_3_5
-- name    : NoRegretLastIterate.claim_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:31:15.669871+00:00
-- url     : https://prove2.me/theorems/06d5549f-a8a5-49ee-8a29-0c3f1947d9d8
-- title:
--   Claim 3.5 — under $Q_t\to q^*$ a.s., almost all rounds have $Q_s\in[q^*/2,(q^*+1)/2]$
-- statement:
--   Let $0<q^*<1$ and let $(Q_t)_{t\ge1}$ be a real-valued random sequence with $Q_t\to q^*$ almost surely. Then almost surely, for every deterministic subsequence $(t_k)_{k\ge1}$,
--   $$
--   \liminf_{k\to\infty}\frac1{t_k}\Big|\Big\{s\le t_k:\ \frac{q^*}2\le Q_s\le\frac{q^*+1}2\Big\}\Big|=1 .
--   $$
--
--   In the paper $Q_t$ is player 2's mixed strategy and $q^*$ the interior Nash equilibrium. The claim provides the lower bound on conditional variances, Eq. (3.22), that makes player 2's realized actions fluctuate at order $1/\sqrt t$ under the hypothesis of almost sure convergence.
--
--   **Formalization Note** $\{s\le t_k\}$ is the set of rounds $1,\dots,t_k$ (Lean $0,\dots,t_k-1$); a subsequence is a strictly increasing map $t:\mathbb N\to\mathbb N$. Since the ratio is at most $1$, $\liminf=1$ is stated as convergence to $1$.
--
--   Differences from the source:
--   - generalization: Q_t player 2's mixed strategy in the play of Theorem 3.4, q∗ the NE → any real-valued process Q on any measure space and any q∗ ∈ (0, 1); reason: the proof is pathwise and uses only Q_t → q∗ and 0 < q∗ < 1; the play is a special case
--   - generalization: "(3.21) almost surely, for any deterministic sub-sequence {t_k}" (for each subsequence, a.s.) → almost surely, for all subsequences simultaneously; reason: the exceptional null set does not depend on the subsequence; this implies the printed order of quantifiers
--   - encoding: lim inf_k (1/t_k)|{s ≤ t_k : …}| = 1 → Tendsto of the ratio to 1; reason: the ratio is at most 1, so lim inf = 1 iff the limit is 1
--   - encoding: rounds t = 1, 2, …; f_t applied to (J)^{t−1} → Lean rounds n = t − 1 from 0; F n applied to the first n actions; reason: Lean convention; same instances
-- source:
--   Muthukumar, Phade, Sahai, On the Impossibility of Convergence of Mixed Strategies with Optimal No-Regret Learning, arXiv:2012.02125v3, Claim 3.5, (3.21), p.17 (proof pp.17–18)

import Mathlib

open MeasureTheory Filter Topology

namespace NoRegretLastIterate

/-- Muthukumar, Phade, Sahai, arXiv:2012.02125v3, Claim 3.5, p.17. If `Q_t → q∗` almost surely,
where `0 < q∗ < 1`, then almost surely, for every deterministic subsequence `{t_k}`,
`lim inf_{k→∞} (1/t_k) |{s ≤ t_k : q∗/2 ≤ Q_s ≤ (q∗ + 1)/2}| = 1` (3.21).

**Formalization Note** `Q` is any real-valued process on any measure space (in the paper it is
player 2's mixed-strategy sequence). The set `{s ≤ t_k}` is the paper's `{1, …, t_k}`, i.e. the
Lean rounds `0, …, t_k − 1`. A subsequence is a strictly increasing `t : ℕ → ℕ`. Since the
ratio is at most `1`, "lim inf = 1" is stated as convergence to `1`. -/
theorem claim_3_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Q : ℕ → Ω → ℝ) {q : ℝ}
    (hq : 0 < q ∧ q < 1) (hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => Q n ω) atTop (𝓝 q)) :
    ∀ᵐ ω ∂μ, ∀ t : ℕ → ℕ, StrictMono t →
      Tendsto (fun k => ((({s ∈ Finset.range (t k) | q / 2 ≤ Q s ω ∧ Q s ω ≤ (q + 1) / 2} :
        Finset ℕ).card : ℝ) / (t k : ℝ))) atTop (𝓝 1) := by sorry

end NoRegretLastIterate
