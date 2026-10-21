-- Prove2me | Theorems.Thm_LeviSampling_BaseStock_error_no_backward_propagation
-- name    : LeviSampling.BaseStock.error_no_backward_propagation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:50:09.292553+00:00
-- url     : https://prove2.me/theorems/e82c1e4b-51ff-46a3-9431-921e8bc23007
-- title:
--   Lemma 3.2 — errors of an upper base-stock policy do not propagate backward
-- statement:
--   Consider the multiperiod model with independent demands of finite mean and costs $h_i, b_i > 0$, periods $0$-based. Let $t + 1 < T$, let $L_{t+1}, \dots, L_{T-1}$ be an upper base-stock policy, let $R_j$ be the smallest minimizer of the optimal cost function $U_j$ for $t \le j < T$, and let $\bar R_t$ be the smallest minimizer of $\tilde U_t$. Suppose that for each $j = t+1, \dots, T-1$ there is $\beta_j \ge 1$ with $\tilde U_j(L_j) \le \beta_j U_j(R_j)$. Then
--   $$\tilde U_t(\bar R_t) \;\le\; \Big(\max_{t < j < T} \beta_j\Big)\, U_t(R_t).$$
--   That is, ordering up to $\bar R_t$ and then following $L$ costs at most $\beta$ times the optimum over the remaining horizon.
--
--   **Formalization Note** The maximum is a real supremum over the finite nonempty index set $\{t+1, \dots, T-1\}$. The paper's "for some $t < T$" (1-based) is $t + 1 < T$ here.
-- source:
--   Levi, Roundy & Shmoys, Provably Near-Optimal Sampling-Based Policies for Stochastic Inventory Control Models, Math. Oper. Res. 32(4) 2007, p. 831, Lemma 3.2

import Mathlib
import Definitions.Def_LeviSampling_BaseStock_Shadow

open MeasureTheory

namespace LeviSampling.BaseStock

/-- **Lemma 3.2** (Levi, Roundy & Shmoys 2007, p. 831), 0-based periods. Let `t + 1 < T`, let
`L_{t+1}, …, L_{T-1}` be an upper base-stock policy, let `R_j` be the smallest minimizer of the
optimal `U_j` (`t ≤ j < T`) and `R̄_t` the smallest minimizer of `Ũ_t`. If for each
`j = t+1, …, T-1` the policy `L_j, …, L_{T-1}` costs `Ũ_j(L_j) ≤ β_j U_j(R_j)` with `β_j ≥ 1`,
then `Ũ_t(R̄_t) ≤ β U_t(R_t)` with `β = max_j β_j`. -/
theorem error_no_backward_propagation (T : ℕ) (μ : ℕ → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, Integrable id (μ i)) (h b : ℕ → ℝ)
    (hh : ∀ i, 0 < h i) (hb : ∀ i, 0 < b i) (L : ℕ → ℝ) (t : ℕ) (ht : t + 1 < T)
    (hL : IsUpperBaseStock T μ h b L (t + 1))
    (R : ℕ → ℝ) (hR : ∀ j, t ≤ j → j < T → IsSmallestMinimizer (optU T μ h b j) (R j))
    (Rbar : ℝ) (hRbar : IsSmallestMinimizer (shadowU T μ h b L t) Rbar)
    (β : ℕ → ℝ) (hβ1 : ∀ j ∈ Finset.Ioo t T, 1 ≤ β j)
    (hβ : ∀ j ∈ Finset.Ioo t T, shadowU T μ h b L j (L j) ≤ β j * optU T μ h b j (R j)) :
    shadowU T μ h b L t Rbar ≤ (⨆ j : Finset.Ioo t T, β j) * optU T μ h b t (R t) := by sorry

end LeviSampling.BaseStock
