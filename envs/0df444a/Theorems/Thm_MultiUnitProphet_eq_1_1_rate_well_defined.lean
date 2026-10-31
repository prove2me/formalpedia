-- Prove2me | Theorems.Thm_MultiUnitProphet_eq_1_1_rate_well_defined
-- name    : MultiUnitProphet.eq_1_1_rate_well_defined
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:37.920366+00:00
-- url     : https://prove2.me/theorems/f006e4e2-03ca-4764-b22f-8e67187af952
-- title:
--   Eq. (1.1) — the Poisson balancing rate $\lambda_k$ is well defined
-- statement:
--   Let $k\ge1$ and let $X^\lambda$ be Poisson with rate $\lambda\ge0$. The truncated expectation $\mu_k(X^\lambda)=\frac1k\mathbb E[\min(X^\lambda,k)]$ is strictly increasing in $\lambda$, equals $0$ at $\lambda=0$ and tends to $1$ as $\lambda\to\infty$; the probability $\delta_k(X^\lambda)=\mathbb P[X^\lambda\le k-1]$ is strictly decreasing, equals $1$ at $\lambda=0$ and tends to $0$. Consequently exactly one rate $\lambda_k\ge0$ satisfies
--
--   $$\frac1k\,\mathbb E[\min(X^{\lambda_k},k)]=\mathbb P[X^{\lambda_k}\le k-1].\qquad(1.1)$$
--
--   This makes the constant $\phi_k$ of Theorem 1 well defined.
--
--   **Formalization Note** Rates are in $\mathbb R_{\ge0}$; "rate equal to infinity" is the limit $\lambda\to\infty$.
--
--   Differences from the source:
--   - encoding: a supply k (a positive integer) → k : ℕ with 1 ≤ k; reason: the supply is a positive number of units; at k = 0 the quantities are degenerate
--   - reading: increases / decreases with the rate → StrictMono / StrictAnti in λ; reason: the paper's derivative argument gives strict monotonicity, which is what makes λ_k unique
--   - encoding: value 1 (resp. 0) for rate equal to infinity → limit as λ → ∞; reason: λ ranges over ℝ≥0; infinity is a limit
--   - reading: this quantity is well defined → ∃! λ ≥ 0 with δ_k(X^λ) = µ_k(X^λ); reason: well-definedness of λ_k is existence and uniqueness of the solution of (1.1)
--   - encoding: a Poisson random variable X^λ with rate λ → deltaPois k λ = Σ_{j<k} e^{−λ}λ^j/j! and muPois k λ = (1/k) Σ_j min{j,k} e^{−λ}λ^j/j!, with λ : ℝ≥0; reason: the Poisson law written through its pmf; same values
-- source:
--   Chawla, Devanur & Lykouris, Static pricing for multi-unit prophet inequalities, arXiv:2007.07990v4, §1.1, eq. (1.1), p.2 and the paragraph on p.3 ("Note that this quantity is well defined")

import Mathlib
import Definitions.Def_MultiUnitProphet_Poisson

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MultiUnitProphet

/-- **The Poisson balancing rate `λ_k` of eq. (1.1) is well defined.**
Chawla, Devanur & Lykouris, *Static pricing for multi-unit prophet inequalities*,
arXiv:2007.07990v4, §1.1, eq. (1.1), p.2 and the text on p.3: "the truncated expectation (1/k) E[min(X, k)]
increases with the rate of the Poisson variable X — it is 0 for rate equal to 0 and 1 for rate
equal to infinity; on the other hand, the probability P[X ≤ k − 1] decreases with the rate — it is
1 when the rate is 0 and 0 when the rate is infinity."

For a supply `k ≥ 1`: `λ ↦ µ_k(X^λ)` is strictly increasing with value `0` at `λ = 0` and limit `1`;
`λ ↦ δ_k(X^λ)` is strictly decreasing with value `1` at `λ = 0` and limit `0`; and exactly one rate
`λ ≥ 0` satisfies (1.1), `µ_k(X^λ) = δ_k(X^λ)`.

**Formalization Note.** Rates are `λ : ℝ≥0`; "rate equal to infinity" is the limit `λ → ∞`.
"Increases"/"decreases" are read strictly. -/
theorem eq_1_1_rate_well_defined (k : ℕ) (hk : 1 ≤ k) :
    StrictMono (muPois k) ∧ muPois k 0 = 0 ∧ Tendsto (muPois k) atTop (𝓝 1) ∧
    StrictAnti (deltaPois k) ∧ deltaPois k 0 = 1 ∧ Tendsto (deltaPois k) atTop (𝓝 0) ∧
    ∃! lam : ℝ≥0, deltaPois k lam = muPois k lam := by sorry

end MultiUnitProphet
