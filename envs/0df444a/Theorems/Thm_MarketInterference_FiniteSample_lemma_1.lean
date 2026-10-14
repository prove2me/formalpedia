-- Prove2me | Theorems.Thm_MarketInterference_FiniteSample_lemma_1
-- name    : MarketInterference.FiniteSample.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:04.793989+00:00
-- url     : https://prove2.me/theorems/04ae9e48-4c84-4a3d-b354-d36061ed896b
-- title:
--   Lemma 1, p. 37 — scaling: (1/τ)Φ_τ(d, s) = Φ(d/τ, s/τ), and optimal flows scale by τ
-- statement:
--   Let $\tau>0$, and let $d\in\mathbb Z^{n_d}_{+}$ and $s\in\mathbb Z^{n_s}_{+}$ be integer demand and supply vectors. Then
--   $$
--   \frac1\tau\,\Phi_\tau(d,s)=\Phi\Big(\frac1\tau d,\frac1\tau s\Big).
--   $$
--   Moreover, a flow $x$ is optimal for $\Phi(\frac1\tau d,\frac1\tau s)$ if and only if $\tau x$ is optimal for $\Phi_\tau(d,s)$.
--
--   The lemma reduces the market at density $\tau$ to the unit-density market with rescaled demand and supply; it is used to pass from rational to integer perturbations in the local-linearity theorem.
--
--   **Formalization Note** The paper's second sentence ("if $x^*$ and $z^*$ are the respective optimal solutions … then $z^*=\tau x^*$") presupposes unique optima; it is stated here as the correspondence of optimal sets, which is its content without uniqueness.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 37, Lemma 1, (27)

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_NetworkLP

namespace MarketInterference.FiniteSample

theorem lemma_1 {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I]
    (N : MarketInterference.FluidBias.Network nd ns I E) (τ : ℝ) (hτ : 0 < τ) (d : Fin nd → ℕ) (s : Fin ns → ℕ) :
    (1 / τ) * MarketInterference.FluidBias.Phi N τ (fun i => (d i : ℝ)) (fun j => (s j : ℝ)) =
        MarketInterference.FluidBias.Phi N 1 (fun i => (1 / τ) * (d i : ℝ)) (fun j => (1 / τ) * (s j : ℝ)) ∧
      ∀ x : E → ℝ,
        MarketInterference.FluidBias.IsOptimal N 1 (fun i => (1 / τ) * (d i : ℝ)) (fun j => (1 / τ) * (s j : ℝ)) x ↔
          MarketInterference.FluidBias.IsOptimal N τ (fun i => (d i : ℝ)) (fun j => (s j : ℝ)) (fun e => τ * x e) := by sorry

end MarketInterference.FiniteSample
