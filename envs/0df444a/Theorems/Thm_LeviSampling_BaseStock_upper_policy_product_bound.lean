-- Prove2me | Theorems.Thm_LeviSampling_BaseStock_upper_policy_product_bound
-- name    : LeviSampling.BaseStock.upper_policy_product_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:59.285726+00:00
-- url     : https://prove2.me/theorems/c1c5433a-3f68-4249-b187-6971ee57a48c
-- title:
--   §3.2, p. 832, claim following Lemma 3.2 — per-stage relative errors multiply
-- statement:
--   Consider the multiperiod model with independent demands of finite mean and costs $h_i, b_i > 0$, periods $0$-based. Let $L_0, \dots, L_{T-1}$ be an upper base-stock policy over the whole horizon, and suppose that for every $t < T$, with $\bar R_t$ the smallest minimizer of $\tilde U_t$,
--   $$\tilde U_t(L_t) \le (1 + \varepsilon_t)\,\tilde U_t(\bar R_t), \qquad \varepsilon_t \ge 0 .$$
--   Then for every $s < T$
--   $$\tilde U_s(L_s) \;\le\; \prod_{j=s}^{T-1}(1 + \varepsilon_j)\ \cdot\ \min_y U_s(y),$$
--   i.e. the base-stock policy $L_s, \dots, L_{T-1}$ costs at most $\prod_j (1+\varepsilon_j)$ times the optimal expected cost over periods $s, \dots, T-1$.
--
--   **Formalization Note** $\min_y U_s(y)$ is a real infimum of a nonnegative function. The condition $L_t \ge \bar R_t$ is part of the upper base-stock hypothesis.
-- source:
--   Levi, Roundy & Shmoys, Provably Near-Optimal Sampling-Based Policies for Stochastic Inventory Control Models, Math. Oper. Res. 32(4) 2007, p. 832, §3.2, claim following Lemma 3.2

import Mathlib
import Definitions.Def_LeviSampling_BaseStock_Shadow

open MeasureTheory

namespace LeviSampling.BaseStock

/-- **Claim after Lemma 3.2** (Levi, Roundy & Shmoys 2007, §3.2, p. 832), 0-based periods. Let
`L_0, …, L_{T-1}` be an upper base-stock policy over the whole horizon such that for every period
`t < T`, with `R̄_t` the smallest minimizer of `Ũ_t`, `Ũ_t(L_t) ≤ (1 + ε_t) Ũ_t(R̄_t)` for some
`ε_t ≥ 0`. Then for every `s < T` the expected cost of the base-stock policy `L_s, …, L_{T-1}`
over periods `s, …, T-1` is at most `∏_{j=s}^{T-1} (1 + ε_j)` times the optimal expected cost
`min_y U_s(y)` over that interval. -/
theorem upper_policy_product_bound (T : ℕ) (μ : ℕ → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, Integrable id (μ i)) (h b : ℕ → ℝ)
    (hh : ∀ i, 0 < h i) (hb : ∀ i, 0 < b i) (L : ℕ → ℝ)
    (hL : IsUpperBaseStock T μ h b L 0)
    (ε : ℕ → ℝ) (hε : ∀ t, t < T → 0 ≤ ε t)
    (Rbar : ℕ → ℝ) (hRbar : ∀ t, t < T → IsSmallestMinimizer (shadowU T μ h b L t) (Rbar t))
    (hgood : ∀ t, t < T →
      shadowU T μ h b L t (L t) ≤ (1 + ε t) * shadowU T μ h b L t (Rbar t)) :
    ∀ s, s < T →
      shadowU T μ h b L s (L s) ≤ (∏ j ∈ Finset.Ico s T, (1 + ε j)) * ⨅ y : ℝ, optU T μ h b s y := by sorry

end LeviSampling.BaseStock
