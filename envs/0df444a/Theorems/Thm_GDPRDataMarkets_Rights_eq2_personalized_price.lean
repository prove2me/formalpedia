-- Prove2me | Theorems.Thm_GDPRDataMarkets_Rights_eq2_personalized_price
-- name    : GDPRDataMarkets.Rights.eq2_personalized_price
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:49.053053+00:00
-- url     : https://prove2.me/theorems/dbdc07ab-b6d3-4577-a522-ea102f56443a
-- title:
--   Eq. (2), p. 13 — r*_M(v, p₂) = (μ − σ)v + min{v, p₂} − c when 2(κ_L v − c) ≥ κ_H v − c ≥ 0
-- statement:
--   Let $v\in[0,1]$ satisfy
--   $$2(\kappa_Lv-c)\ \ge\ \kappa_Hv-c\ \ge\ 0.$$
--   Then for every basic price $p_2\in\mathbb R$ the personalized price
--   $$r^*_M(v,p_2)=(\mu-\sigma)v+\min\{v,p_2\}-c$$
--   maximizes the firm's expected second-period revenue from the opted-in consumer $v$. At this price both the $\kappa_L$ and the $\kappa_H$ consumer keep their data and buy the personalized good.
--
--   The formula combines the case $v\ge p_2$ (price $\kappa_Lv+p_2-c$) and the case $p_2>v$ (price $(1+\kappa_L)v-c$); note $\mu-\sigma=\kappa_L$. It is the personalized price paid in the equilibrium of Proposition 1, and it makes the low type exactly indifferent between keeping and erasing her data.
--
--   **Formalization Note** The page states the condition for $p_2>v$ as $2((1+\kappa_L)v-c)\ge(1+\kappa_H)v-c\ge0$; for $v\ge0$ it follows from the condition above, which is the one the page says must be guaranteed for every $v\ge v^*_M(p_1)$. The standing assumptions are hypotheses.
-- source:
--   Ke, Sudhir, Privacy Rights and Data Security: GDPR and Personal Data Markets, SSRN 3643979 (pdfTeX build 2022-09-14), p. 13, eq. (2)

import Mathlib
import Definitions.Def_GDPRDataMarkets_Rights_Model

namespace GDPRDataMarkets.Rights

/-- Eq. (2), p. 13: when `2(κ_L v − c) ≥ κ_H v − c ≥ 0`, at every basic price `p₂` the price
`r*_M(v, p₂) = (μ − σ)v + min{v, p₂} − c` maximizes the expected revenue from the opted-in consumer
`v`, and both types keep their data and buy the personalized good at that price. -/
theorem eq2_personalized_price (P : Params) (hS : P.Standing) (v : ℝ)
    (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (hcase : P.kH * v - P.c ≤ 2 * (P.kL * v - P.c) ∧ 0 ≤ P.kH * v - P.c) (q : ℝ) :
    (∀ ρ : ℝ, R P v q ρ ≤ R P v q ((P.mu - P.sigma) * v + min v q - P.c)) ∧
    keeps P v P.kL q ((P.mu - P.sigma) * v + min v q - P.c) ∧
    keeps P v P.kH q ((P.mu - P.sigma) * v + min v q - P.c) := by sorry

end GDPRDataMarkets.Rights
