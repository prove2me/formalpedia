-- Prove2me | Theorems.Thm_MarketInterference_FluidLimit_lemma_1
-- name    : MarketInterference.FluidLimit.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:17.044353+00:00
-- url     : https://prove2.me/theorems/f2dc9dce-ed9b-47cf-a8a9-f2d94ace51ac
-- title:
--   Lemma 1, p. 37 — (1/τ)Φ_τ(d, s) = Φ(d/τ, s/τ), and x optimal for Φ(d/τ, s/τ) iff τx optimal for Φ_τ(d, s)
-- statement:
--   Let $d\in\mathbb Z^{n_d}_+$ be a demand vector, $s\in\mathbb Z^{n_s}_+$ a supply vector and $\tau>0$ a density. Then the value of the matching program (2) scales as
--
--   $$
--   \frac1\tau\,\Phi_\tau(d,s)=\Phi\Big(\frac1\tau d,\frac1\tau s\Big),
--   $$
--
--   and a flow $x$ is optimal for $\Phi(\frac1\tau d,\frac1\tau s)$ if and only if $\tau x$ is optimal for $\Phi_\tau(d,s)$.
--
--   The identity converts the expected scaled value $\mathbb E[\frac1\tau\Phi_\tau(D^\tau,S^\tau)]$ into $\mathbb E[\Phi(\frac1\tau D^\tau,\frac1\tau S^\tau)]$, the form in which the fluid limit is taken.
--
--   **Formalization Note** The paper's second sentence ("if $x^*$ and $z^*$ are the respective optimal primal solutions … then $z^*=\tau x^*$") presupposes unique optima; it is stated here as the equivalence of optimality under $x\mapsto\tau x$, which is the paper's claim when the optima are unique. The density $\tau$ is any positive real.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 37, Lemma 1, (27)

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_NetworkLP

namespace MarketInterference.FluidLimit

/-- Lemma 1 (arXiv:2205.02274v4, p. 37, (27)): for integer demand and supply vectors and every
density `τ > 0`, `(1/τ) Φ_τ(d, s) = Φ((1/τ) d, (1/τ) s)`, and `x` is optimal for the right-hand side
iff `τ x` is optimal for the left-hand side. -/
theorem lemma_1 {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I]
    (N : MarketInterference.FluidBias.Network nd ns I E) (τ : ℝ) (hτ : 0 < τ) (d : Fin nd → ℕ) (s : Fin ns → ℕ) :
    (1 / τ) * MarketInterference.FluidBias.Phi N τ (fun i => (d i : ℝ)) (fun j => (s j : ℝ)) =
        MarketInterference.FluidBias.Phi N 1 (fun i => 1 / τ * (d i : ℝ)) (fun j => 1 / τ * (s j : ℝ)) ∧
      ∀ x : E → ℝ, MarketInterference.FluidBias.IsOptimal N 1 (fun i => 1 / τ * (d i : ℝ)) (fun j => 1 / τ * (s j : ℝ)) x ↔
        MarketInterference.FluidBias.IsOptimal N τ (fun i => (d i : ℝ)) (fun j => (s j : ℝ)) (τ • x) := by sorry

end MarketInterference.FluidLimit
