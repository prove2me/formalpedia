-- Prove2me | Theorems.Thm_MarketInterference_FiniteSample_theorem_7
-- name    : MarketInterference.FiniteSample.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:08.475867+00:00
-- url     : https://prove2.me/theorems/f0bd7127-def1-44e8-b502-dff774012717
-- title:
--   Theorem 7, p. 24 — local linearity of Φ_τ around integer demand: (15) and (16)
-- statement:
--   Consider the matching problem at density $\tau>0$ with integer demand $d\in\mathbb Z^{n_d}_+$ and integer supply $s\in\mathbb Z^{n_s}_+$, and assume every scaled capacity is an integer, $k_{u,w}\tau\in\mathbb Z$. Let $\varepsilon\in\mathbb R^{n_d}_+$ with $\sum_i\varepsilon_i\le1$, and let $e_i$ be the $i$-th unit vector. Then
--   $$
--   \Phi_\tau(d+\varepsilon,s)=\Phi_\tau(d,s)+\sum_{i=1}^{n_d}\varepsilon_i\big[\Phi_\tau(d+e_i,s)-\Phi_\tau(d,s)\big]. \tag{15}
--   $$
--   If moreover $d_i\ge1$ for every $i$ with $\varepsilon_i>0$, then
--   $$
--   \Phi_\tau(d-\varepsilon,s)=\Phi_\tau(d,s)-\sum_{i=1}^{n_d}\varepsilon_i\big[\Phi_\tau(d,s)-\Phi_\tau(d-e_i,s)\big]. \tag{16}
--   $$
--
--   The matching value is therefore linear on the simplex spanned by $d$ and its upward (respectively downward) unit neighbours, and the one-unit differences $a^+_i$ and $a^-_i$ are subgradients of $\Phi_\tau(\cdot,s)$ at $d$.
--
--   **Formalization Note** If $d_i=0$ and $\varepsilon_i>0$, both sides of (16) involve an infeasible program (value $-\infty$ in LP convention); the hypothesis $d_i\ge1$ for such $i$ is added to (16) only, and (15) is stated without it. The density $\tau>0$ is the paper's standing setting.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 24, Theorem 7, (15)–(16)

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_NetworkLP

namespace MarketInterference.FiniteSample

theorem theorem_7 {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I]
    (N : MarketInterference.FluidBias.Network nd ns I E) (τ : ℝ) (hτ : 0 < τ) (hk : ∀ e, ∃ n : ℕ, τ * N.k e = n)
    (d : Fin nd → ℕ) (s : Fin ns → ℕ) (ε : Fin nd → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (hsum : ∑ i, ε i ≤ 1) :
    MarketInterference.FluidBias.Phi N τ ((fun i => (d i : ℝ)) + ε) (fun j => (s j : ℝ)) =
        MarketInterference.FluidBias.Phi N τ (fun i => (d i : ℝ)) (fun j => (s j : ℝ)) +
          ∑ i, ε i * (MarketInterference.FluidBias.Phi N τ ((fun i => (d i : ℝ)) + Pi.single i 1) (fun j => (s j : ℝ)) -
            MarketInterference.FluidBias.Phi N τ (fun i => (d i : ℝ)) (fun j => (s j : ℝ))) ∧
      ((∀ i, 0 < ε i → 1 ≤ d i) →
        MarketInterference.FluidBias.Phi N τ ((fun i => (d i : ℝ)) - ε) (fun j => (s j : ℝ)) =
          MarketInterference.FluidBias.Phi N τ (fun i => (d i : ℝ)) (fun j => (s j : ℝ)) -
            ∑ i, ε i * (MarketInterference.FluidBias.Phi N τ (fun i => (d i : ℝ)) (fun j => (s j : ℝ)) -
              MarketInterference.FluidBias.Phi N τ ((fun i => (d i : ℝ)) - Pi.single i 1) (fun j => (s j : ℝ)))) := by sorry

end MarketInterference.FiniteSample
