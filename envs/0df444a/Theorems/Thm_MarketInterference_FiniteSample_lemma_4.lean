-- Prove2me | Theorems.Thm_MarketInterference_FiniteSample_lemma_4
-- name    : MarketInterference.FiniteSample.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:56.65598+00:00
-- url     : https://prove2.me/theorems/a95403d8-c5ad-44dc-8715-2c32eee652b5
-- title:
--   Lemma 4, p. 52 — ∂/∂λ_i E[Φ(D, S)] = E[A⁺_i] for Poisson demand and supply
-- statement:
--   Fix a matching network with arbitrary capacities $k\ge0$, and let $\Phi=\Phi_1$. Let $D_i\sim\mathrm{Poisson}(\lambda_i)$ for each demand type $i$ and $S_j\sim\mathrm{Poisson}(\pi_j)$ for each supply type $j$, all independent, with $\lambda,\pi\ge0$. If $\lambda_i>0$, then $\mathbb E[\Phi(D,S)]$ is differentiable in $\lambda_i$ (the other rates held fixed) and
--   $$
--   \frac{\partial}{\partial\lambda_i}\mathbb E[\Phi(D,S)]=\mathbb E\big[A^+_i\big],\qquad A^+_i=\Phi(D+e_i,S)-\Phi(D,S).
--   $$
--
--   Combined with the chain rule, this gives the derivative of the partial-treatment value function $\Psi_\tau$ along the direction $\beta$.
--
--   **Formalization Note** $A^+_i$ is the positive-demand subgradient (17) at $(D,S)$. The paper states the lemma for $\Phi=\Phi_1$; Theorem 6 needs it for $\Phi_\tau$, which is $\Phi_1$ on the same network with capacities $\tau k$, so the lemma is stated for an arbitrary network (any capacities $k\ge 0$). The partial derivative is `HasDerivAt` of $t\mapsto\mathbb E[\Phi(D,S)]$ with the $i$-th rate replaced by $t$, at $t=\lambda_i$.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 52, Lemma 4

import Mathlib
import Definitions.Def_MarketInterference_FiniteSample_Experiment

namespace MarketInterference.FiniteSample

open MeasureTheory ProbabilityTheory

theorem lemma_4 {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I]
    (N : MarketInterference.FluidBias.Network nd ns I E) (lam : Fin nd → ℝ) (pi : Fin ns → ℝ) (hlam : 0 ≤ lam) (hpi : 0 ≤ pi)
    (i : Fin nd) (hi : 0 < lam i) :
    HasDerivAt
      (fun t : ℝ => ∫ z, MarketInterference.FluidBias.Phi N 1 (fun k => (z.1 k : ℝ)) (fun j => (z.2 j : ℝ))
        ∂((poisLaw (Function.update lam i t)).prod (poisLaw pi)))
      (∫ z, Aplus N 1 (fun k => (z.1 k : ℝ)) (fun j => (z.2 j : ℝ)) i
        ∂((poisLaw lam).prod (poisLaw pi)))
      (lam i) := by sorry

end MarketInterference.FiniteSample
