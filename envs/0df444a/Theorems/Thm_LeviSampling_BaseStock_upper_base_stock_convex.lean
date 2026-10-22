-- Prove2me | Theorems.Thm_LeviSampling_BaseStock_upper_base_stock_convex
-- name    : LeviSampling.BaseStock.upper_base_stock_convex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:50:01.421036+00:00
-- url     : https://prove2.me/theorems/759e9d6f-2a8c-4b52-b109-e1422e7c4bdf
-- title:
--   Lemma 3.1 — an upper base-stock policy keeps the shadow dynamic program convex
-- statement:
--   Consider the multiperiod model with independent demands of finite mean and costs $h_i, b_i > 0$. Let $L_{t+1}, \dots, L_{T-1}$ be an upper base-stock policy (periods $0$-based, $t < T$). Then for every period $j$ with $t \le j < T$:
--
--   (i) the shadow functions $\tilde U_j$ and $\tilde V_j = \min_{y\ge \cdot}\tilde U_j(y)$ are convex and $\tilde U_j$ attains its minimum;
--
--   (ii) $\bar R_j$ exists: $\tilde U_j$ is convex and has a smallest minimizer.
--   $$\tilde U_j,\ \tilde V_j \text{ convex},\qquad \exists\, \bar R_j = \text{smallest minimizer of } \tilde U_j .$$
--   This is the invariant that keeps every stage of the sampling algorithm a convex one-dimensional problem.
--
--   **Formalization Note** Paper period $t$ is period $t-1$ here; the paper's interval $[t+1, T]$ is the hypothesis `IsUpperBaseStock … (t + 1)`. Finite mean demand ($\mathbb E|D_i| < \infty$, p. 824) is an explicit hypothesis.
-- source:
--   Levi, Roundy & Shmoys, Provably Near-Optimal Sampling-Based Policies for Stochastic Inventory Control Models, Math. Oper. Res. 32(4) 2007, p. 831, Lemma 3.1

import Mathlib
import Definitions.Def_LeviSampling_BaseStock_Shadow

open MeasureTheory

namespace LeviSampling.BaseStock

/-- **Lemma 3.1** (Levi, Roundy & Shmoys 2007, p. 831), 0-based periods. If the levels
`L_{t+1}, …, L_{T-1}` form an upper base-stock policy, then for every period `j` with
`t ≤ j < T`: (i) `Ũ_j` and `Ṽ_j` are convex and `Ũ_j` attains a minimum; (ii) `R̄_j` exists
(`Ũ_j` is convex with a smallest minimizer). Demands are independent with integrable laws `μ i`;
costs `h i, b i > 0`. -/
theorem upper_base_stock_convex (T : ℕ) (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable id (μ i)) (h b : ℕ → ℝ) (hh : ∀ i, 0 < h i) (hb : ∀ i, 0 < b i)
    (L : ℕ → ℝ) (t : ℕ) (ht : t < T) (hL : IsUpperBaseStock T μ h b L (t + 1)) :
    ∀ j, t ≤ j → j < T →
      (ConvexOn ℝ Set.univ (shadowU T μ h b L j) ∧
        ConvexOn ℝ Set.univ (shadowV T μ h b L j) ∧
        ∃ y, ∀ z, shadowU T μ h b L j y ≤ shadowU T μ h b L j z) ∧
      ∃ r, IsShadowLevel T μ h b L j r := by sorry

end LeviSampling.BaseStock
