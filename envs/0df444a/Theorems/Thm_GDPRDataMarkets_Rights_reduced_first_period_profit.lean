-- Prove2me | Theorems.Thm_GDPRDataMarkets_Rights_reduced_first_period_profit
-- name    : GDPRDataMarkets.Rights.reduced_first_period_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:09.671974+00:00
-- url     : https://prove2.me/theorems/8c57abe1-f04a-4491-977b-9ac1b6996715
-- title:
--   §3.1, p. 15 — the firm's profit at every p₁ equals the reduced profit p₁(1 − min{v*_M, p₁}) + (δ/2)(1 − min{1/2, v*_M²}) + …
-- statement:
--   Assume the standing assumptions and Assumption 1. Let $s$ be a strategy profile in which
--   1. every personalized price maximizes the firm's expected revenue from the consumer it is offered to,
--   2. after every first-period price, the basic price maximizes the firm's second-period profit, and
--   3. after every first-period price, every consumer's first-period action is optimal.
--
--   Then for every real $p_1$, the firm's total profit at $p_1$ equals
--   $$p_1\big(1-\min\{v^*_M(p_1),p_1\}\big)+\frac{\delta}{2}\Big(1-\min\Big\{\frac12,v^*_M(p_1)^2\Big\}\Big)+\frac{\delta}{2}(\mu-\sigma)\big(1-v^*_M(p_1)^2\big)-\delta\big(1-v^*_M(p_1)\big)c,$$
--   with $v^*_M(p_1)$ clipped to $[0,1]$ and $p_1$ clipped below at $0$ inside the first minimum.
--
--   This reduces the firm's first-period problem, a problem about the whole game, to the maximization of an explicit piecewise quadratic function of $p_1$.
--
--   **Formalization Note** The profile need not satisfy the fourth equilibrium condition (optimality of $s.p_1$). Ties of consumers (at $v=v^*_M(p_1)$ and $v=p_1$) and of the firm (at $v^*_M(p_1)=1/\sqrt2$) do not affect the value. The clipping extends the page's formula, written for $p_1\ge0$ and $v^*_M(p_1)\le1$, to all real $p_1$.
-- source:
--   Ke, Sudhir, Privacy Rights and Data Security: GDPR and Personal Data Markets, SSRN 3643979 (pdfTeX build 2022-09-14), p. 15, the firm's first-period profit maximization problem

import Mathlib
import Definitions.Def_GDPRDataMarkets_Rights_Model
import Definitions.Def_GDPRDataMarkets_Rights_ClosedForms

namespace GDPRDataMarkets.Rights

/-- §3.1, p. 15: when the personalized prices, the basic price after every first-period price and
the consumers' first-period actions are optimal, the firm's total profit at every first-period price
`p₁` equals the reduced profit
`p₁(1 − min{v*, p₁}) + (δ/2)(1 − min{1/2, v*²}) + (δ/2)(μ − σ)(1 − v*²) − δ(1 − v*)c`
(with `v*` clipped to `[0, 1]` and `p₁` clipped at `0` inside the `min`). -/
theorem reduced_first_period_profit (P : Params) (hS : P.Standing) (hA : P.Assumption1)
    (s : Profile)
    (h1 : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ q ρ : ℝ, R P v q ρ ≤ R P v q (s.r v q))
    (h2 : ∀ p1 q : ℝ, profit2 P s p1 q ≤ profit2 P s p1 (s.p2 p1))
    (h3 : ∀ p1 : ℝ, ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ a : FirstChoice,
      U1 P s p1 v a ≤ U1 P s p1 v (s.choice p1 v)) :
    ∀ p1 : ℝ, profit P s p1 = profitRed P p1 := by sorry

end GDPRDataMarkets.Rights
