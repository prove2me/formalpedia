-- Prove2me | Theorems.Thm_GDPRDataMarkets_Benchmark_personalized_price
-- name    : GDPRDataMarkets.Benchmark.personalized_price
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:00.674989+00:00
-- url     : https://prove2.me/theorems/59593af1-b9b5-42ed-8eaa-66c3bbc15e63
-- title:
--   Proof of Prop. 2, p. 49 — the personalized price r^B_M(v) = (1 + κ_L)v = (1 + μ − σ)v is optimal and both types keep buying
-- statement:
--   Consider the benchmark model without privacy rights. The parameters satisfy $\kappa_H>\kappa_L>0$, $\delta\in(0,1]$ and $c\ge0$, with $\mu=(\kappa_H+\kappa_L)/2$ and $\sigma=(\kappa_H-\kappa_L)/2$, and moreover $\mu\ge3\sigma-1$. Let $v\ge0$ be the valuation of a first-period buyer, and let
--   $$R(v,\rho)=\frac{\rho}{2}\Big[\mathbb 1\big(\rho\le(1+\kappa_L)v\big)+\mathbb 1\big(\rho\le(1+\kappa_H)v\big)\Big]$$
--   be the firm's expected revenue from her at the personalized price $\rho$. Then the price $(1+\mu-\sigma)v=(1+\kappa_L)v$ maximizes $R(v,\cdot)$ over all real $\rho$:
--   $$R(v,\rho)\ \le\ R\big(v,(1+\mu-\sigma)v\big)\qquad\text{for all }\rho\in\mathbb R.$$
--   At this price $(1+\mu-\sigma)v\le(1+\kappa_L)v$ and $(1+\mu-\sigma)v\le(1+\kappa_H)v$, so consumers of both types continue to buy in the second period.
--
--   This determines the second-period personalized price in every regime of Proposition 2.
--
--   **Formalization Note.** The page's condition $\mu\ge3\sigma-1$ is the hypothesis; Assumption 1 implies it. "Continue to purchase" is encoded by the convention that an indifferent consumer buys, i.e. a type $\kappa$ buys iff $\rho\le(1+\kappa)v$.
-- source:
--   Ke, Sudhir, Privacy Rights and Data Security: GDPR and Personal Data Markets, SSRN 3643979 (pdfTeX build 2022-09-14), p. 49, Appendix, proof of Proposition 2, first display

import Mathlib
import Definitions.Def_GDPRDataMarkets_Benchmark_Model

namespace GDPRDataMarkets.Benchmark
theorem personalized_price (P : Params) (hS : P.Standing) (hμ : 3 * P.sigma - 1 ≤ P.mu)
    (v : ℝ) (hv : 0 ≤ v) :
    (∀ ρ : ℝ, RB P v ρ ≤ RB P v ((1 + P.mu - P.sigma) * v)) ∧
    (1 + P.mu - P.sigma) * v = (1 + P.kL) * v ∧
    (1 + P.mu - P.sigma) * v ≤ (1 + P.kL) * v ∧
    (1 + P.mu - P.sigma) * v ≤ (1 + P.kH) * v := by sorry
end GDPRDataMarkets.Benchmark
