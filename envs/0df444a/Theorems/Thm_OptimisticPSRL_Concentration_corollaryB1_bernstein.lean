-- Prove2me | Theorems.Thm_OptimisticPSRL_Concentration_corollaryB1_bernstein
-- name    : OptimisticPSRL.Concentration.corollaryB1_bernstein
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:39:48.136825+00:00
-- url     : https://prove2.me/theorems/e454b8ef-f79b-4ad3-9ddb-cc0772e4a3b6
-- title:
--   Corollary B.1, p. 26 — Bernstein for bounded martingale differences: |Mₙ| ≤ 2√(Vₙ ln(n/δ)) + 3K ln(n/δ)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space with a filtration $(\mathcal F_i)_{i\ge0}$, and let $Z_1,\dots,Z_n$ be a bounded martingale difference sequence: $Z_i$ is $\mathcal F_i$-measurable, $|Z_i|\le K$ and $\mathbb E[Z_i\mid\mathcal F_{i-1}]=0$. Put
--
--   $$
--   M_n=\sum_{i=1}^nZ_i,\qquad V_n=\sum_{i=1}^n\mathbb E\big[Z_i^2\mid\mathcal F_{i-1}\big].
--   $$
--
--   If $n\ge96$ and $\delta\in(0,1)$, then with probability greater than $1-\delta$,
--
--   $$
--   |M_n|\le2\sqrt{V_n\ln\frac n\delta}+3K\ln\frac n\delta .
--   $$
--
--   This is a Bernstein inequality with the random predictable variance $V_n$ in place of a deterministic variance bound, at the price of $\ln(n/\delta)$ instead of $\ln(1/\delta)$. Agrawal and Jia derive it from a result of Seldin et al. (2012) and use it to prove Proposition 5.2.
--
--   **Formalization Note** Indices are shifted: $Z_i$ is `Z i` for $i=1,\dots,n$, measurable for `ℱ i`, with conditional expectation taken given `ℱ (i-1)`. The bound $|Z_i|\le K$ is required almost surely. "With probability greater than $1-\delta$" is the strict inequality $1-\delta<\mathbb P(\cdot)$, as printed.
-- source:
--   Agrawal & Jia, Posterior sampling for reinforcement learning: worst-case regret bounds, arXiv:1705.07041v3, p. 26, Appendix B, Corollary B.1 (setting from Fact 3)

import Mathlib

namespace OptimisticPSRL.Concentration

open MeasureTheory

/-- **Corollary B.1** (Agrawal–Jia, arXiv:1705.07041v3, p. 26). Let `Z_1, …, Z_n` be a
martingale difference sequence for the filtration `ℱ` (`Z_i` is `ℱ_i`-measurable and
`E[Z_i | ℱ_{i−1}] = 0`) with `|Z_i| ≤ K`, `M_n = ∑_{i=1}^n Z_i` and
`V_n = ∑_{i=1}^n E[Z_i² | ℱ_{i−1}]`. For `n ≥ 96` and `δ ∈ (0, 1)`, with probability greater
than `1 − δ`, `|M_n| ≤ 2 √(V_n ln(n/δ)) + 3K ln(n/δ)`. -/
theorem corollaryB1_bernstein {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (Z : ℕ → Ω → ℝ) (K : ℝ) (n : ℕ) (δ : ℝ)
    (hmeas : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (Z (i + 1)))
    (hbdd : ∀ i < n, ∀ᵐ ω ∂μ, |Z (i + 1) ω| ≤ K)
    (hmds : ∀ i < n, μ[Z (i + 1) | ℱ i] =ᵐ[μ] 0)
    (hn : 96 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) <
      μ {ω | |∑ i ∈ Finset.range n, Z (i + 1) ω| ≤
        2 * Real.sqrt ((∑ i ∈ Finset.range n, (μ[fun ω' => Z (i + 1) ω' ^ 2 | ℱ i]) ω) *
            Real.log (n / δ)) +
          3 * K * Real.log (n / δ)} := by sorry

end OptimisticPSRL.Concentration
