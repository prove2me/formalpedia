-- Prove2me | Theorems.Thm_MarketInterference_FiniteSample_theorem_6
-- name    : MarketInterference.FiniteSample.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:47.839005+00:00
-- url     : https://prove2.me/theorems/8232580d-dcd3-4710-927c-7610627485e7
-- title:
--   Theorem 6, p. 24 — for every τ > 0, E[Δ̂^τ_SP] = Ψ′_τ(ρ)
-- statement:
--   Fix a matching network (any finite set of intermediate nodes, any arc values, any capacities $k\ge0$), a control demand rate $\lambda\ge0$, a treatment effect $\beta$ with $\lambda+\beta\ge0$, a supply rate $\pi\ge0$, a treatment fraction $\rho\in(0,1)$ and a density $\tau>0$. Let $\Psi_\tau(\eta)=\mathbb E\big[\frac1\tau\Phi_\tau(D^{\tau,\lambda+\eta\beta},S^{\tau,\pi})\big]$ be the finite-sample partial-treatment value function, and let $\hat\Delta^\tau_{SP}$ be the shadow-price estimator computed from the experiment's independent control counts $D^{\tau,\mathrm{control}}_i\sim\mathrm{Poisson}((1-\rho)\lambda_i\tau)$, treatment counts $D^{\tau,\mathrm{treatment}}_i\sim\mathrm{Poisson}(\rho(\lambda_i+\beta_i)\tau)$ and supply counts $S^\tau_j\sim\mathrm{Poisson}(\pi_j\tau)$, with the negative-demand subgradient $A^-$ of the experiment LP. Then $\Psi_\tau$ is differentiable at $\rho$ and
--   $$
--   \mathbb E\big[\hat\Delta^\tau_{SP}\big]=\frac{\partial}{\partial\eta}\,\mathbb E\Big[\frac1\tau\Phi_\tau(D^{\tau,\lambda+\eta\beta},S^{\tau,\pi})\Big]\Big|_{\eta=\rho}=\Psi_\tau'(\rho). \tag{14}
--   $$
--
--   In expectation, the shadow-price estimator measures the slope of the partial-treatment value function at the experiment state, at every finite market size and with no uniqueness assumption on the optimal duals. Combined with a bound on $\Psi_\tau''$ it bounds the estimator's expected bias (Corollary 2).
--
--   **Formalization Note** The expectation of $\hat\Delta^\tau_{SP}$ is taken under the product law of the control, treatment and supply counts (not under the law of the total demand). The derivative is asserted with `HasDerivAt`, so differentiability is part of the conclusion. Assumptions 1–3 of the paper (random tie-breaking, unique optima of the fluid LP, sign-consistent $\beta$) are not hypotheses: the proof on pp. 53–55 uses none of them, and the selection $A=A^-$ is what makes the identity hold without uniqueness (p. 25). No integrality of capacities is assumed.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 24, Theorem 6, (14)

import Mathlib
import Definitions.Def_MarketInterference_FiniteSample_Experiment

namespace MarketInterference.FiniteSample

open MeasureTheory ProbabilityTheory

theorem theorem_6 {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I]
    (N : MarketInterference.FluidBias.Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ)
    (hlam : 0 ≤ lam) (hlamb : 0 ≤ lam + beta) (hpi : 0 ≤ pi)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (τ : ℝ) (hτ : 0 < τ) :
    HasDerivAt (PsiTau N lam beta pi τ)
      (∫ z, SPest N ρ τ z.1.1 z.1.2 z.2 ∂(experimentLaw lam beta pi ρ τ)) ρ := by sorry

end MarketInterference.FiniteSample
