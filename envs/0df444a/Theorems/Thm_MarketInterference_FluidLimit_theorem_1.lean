-- Prove2me | Theorems.Thm_MarketInterference_FluidLimit_theorem_1
-- name    : MarketInterference.FluidLimit.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:00.901809+00:00
-- url     : https://prove2.me/theorems/6e073256-5860-42ee-afdb-b9cab4111592
-- title:
--   Theorem 1, (7), p. 12 — E[(1/τ)Φ_τ(D^{τ,λ}, S^τ)] → Φ(λ, π) as τ → ∞
-- statement:
--   Consider a matching network with values $v_{u,w}$ and capacities $k_{u,w}\ge 0$, demand rates $\lambda\in\mathbb R^{n_d}_{\ge 0}$ and supply rates $\pi\in\mathbb R^{n_s}_{\ge 0}$. For each integer density $\tau$ let $D^{\tau,\lambda}_i\sim\mathrm{Poisson}(\lambda_i\tau)$ and $S^\tau_j\sim\mathrm{Poisson}(\pi_j\tau)$ be independent counts, and let $\Phi_\tau$ be the optimal value of the matching program (2) with capacities $\tau k$. Then
--
--   $$
--   \lim_{\tau\to\infty}\mathbb E\Big[\frac1\tau\,\Phi_\tau\big(D^{\tau,\lambda},S^\tau\big)\Big]=\Phi(\lambda,\pi).
--   $$
--
--   In words: in a dense market the expected matching value per unit of density is the value of the deterministic linear program whose demand and supply are the arrival rates. This is what lets the rest of the paper study treatment effects through the fluid program $\Phi(\lambda,\pi)$ instead of the stochastic system.
--
--   **Formalization Note** The limit is taken along integer $\tau\to\infty$ ("we only consider integer densities τ", p. 12); at $\tau=0$ Lean's $1/0=0$ gives a junk term that does not affect the limit. The expectation is the Bochner integral against the product of the independent Poisson laws; the integrand is bounded ($0\le\frac1\tau\Phi_\tau\le\sum|v_{u,w}|k_{u,w}$) and every function on the countable count space is measurable, so it is integrable. Only the first sentence of Theorem 1, display (7), is stated; the second sentence (almost-sure convergence of optimal primal and dual solutions) needs unique optima, assumed only inside the proof, and a coupling of the counts across $\tau$ that the paper does not construct.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 12, Theorem 1, (7)

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_NetworkLP
import Definitions.Def_MarketInterference_FluidLimit_PoissonCounts

namespace MarketInterference.FluidLimit

open MeasureTheory Filter Topology

/-- Theorem 1, display (7) (arXiv:2205.02274v4, p. 12): along integer densities `τ → ∞`,
`E[(1/τ) Φ_τ(D^{τ,λ}, S^τ)] → Φ(λ, π)`, where `D^{τ,λ}_i ∼ Poisson(λ_i τ)` and `S^τ_j ∼ Poisson(π_j τ)`
are independent. -/
theorem theorem_1 {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I]
    (N : MarketInterference.FluidBias.Network nd ns I E) (lam : Fin nd → ℝ) (pi : Fin ns → ℝ) (hlam : 0 ≤ lam) (hpi : 0 ≤ pi) :
    Tendsto (fun τ : ℕ => ∫ z, (1 / (τ : ℝ)) * MarketInterference.FluidBias.Phi N τ (fun i => (z.1 i : ℝ)) (fun j => (z.2 j : ℝ))
        ∂(fluidLaw lam pi τ)) atTop (𝓝 (MarketInterference.FluidBias.Phi N 1 lam pi)) := by sorry

end MarketInterference.FluidLimit
