-- Prove2me | Theorems.Thm_GDPRDataMarkets_Rights_eq1_personalized_price
-- name    : GDPRDataMarkets.Rights.eq1_personalized_price
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:48.312085+00:00
-- url     : https://prove2.me/theorems/3433a1c2-06c6-48d7-9c9b-36e28eef6352
-- title:
--   Eq. (1), p. 13 — the optimal personalized price r*_M(v, p₂) in the three cases, for v ≥ p₂
-- statement:
--   Consider an opted-in consumer with valuation $v\in[0,1]$, a basic price $p_2\le v$, and the firm's expected second-period revenue $R(v,p_2,r)$ from this consumer at personalized price $r$, where $\kappa\in\{\kappa_L,\kappa_H\}$ is equally likely and unknown to the firm. Then:
--
--   1. if $2(\kappa_Lv-c)\ge\kappa_Hv-c\ge 0$, the price $r=\kappa_Lv+p_2-c$ maximizes $R(v,p_2,\cdot)$;
--   2. if $\kappa_Hv-c\ge\max\{2(\kappa_Lv-c),0\}$, the price $r=\kappa_Hv+p_2-c$ maximizes it;
--   3. if $0\ge\max\{\kappa_Hv-c,\ 2(\kappa_Lv-c)\}$, every price $r>\kappa_Hv+p_2-c$ maximizes it.
--
--   In summary,
--   $$r^*_M(v,p_2)\ \begin{cases}=\kappa_Lv+p_2-c & \text{in case (i)},\\ =\kappa_Hv+p_2-c & \text{in case (ii)},\\ >\kappa_Hv+p_2-c & \text{in case (iii)}.\end{cases}$$
--
--   In case (i) both types buy the personalized good, in case (ii) only the high type, and in case (iii) both types erase their data and buy the basic good. This is the firm's second-period pricing problem; the equilibrium uses case (i).
--
--   **Formalization Note** The standing assumptions $\kappa_H>\kappa_L>0$, $\delta\in(0,1]$, $c\ge0$ are hypotheses. An opted-in consumer keeps her data on a tie and, after erasing, buys the basic good iff $v\ge p_2$; with the page's strict rule $v-p_2>\dots$, cases (ii) and (iii) would fail at $v=p_2$.
-- source:
--   Ke, Sudhir, Privacy Rights and Data Security: GDPR and Personal Data Markets, SSRN 3643979 (pdfTeX build 2022-09-14), p. 13, eq. (1)

import Mathlib
import Definitions.Def_GDPRDataMarkets_Rights_Model

namespace GDPRDataMarkets.Rights

/-- Eq. (1), p. 13: for `v ≥ p₂`, the optimal personalized price is `κ_L v + p₂ − c` in case (i),
`κ_H v + p₂ − c` in case (ii), and any price above `κ_H v + p₂ − c` in case (iii). -/
theorem eq1_personalized_price (P : Params) (hS : P.Standing) (v q : ℝ)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) (hq : q ≤ v) :
    (P.kH * v - P.c ≤ 2 * (P.kL * v - P.c) ∧ 0 ≤ P.kH * v - P.c →
        ∀ ρ : ℝ, R P v q ρ ≤ R P v q (P.kL * v + q - P.c)) ∧
    (max (2 * (P.kL * v - P.c)) 0 ≤ P.kH * v - P.c →
        ∀ ρ : ℝ, R P v q ρ ≤ R P v q (P.kH * v + q - P.c)) ∧
    (max (P.kH * v - P.c) (2 * (P.kL * v - P.c)) ≤ 0 →
        ∀ ρ : ℝ, P.kH * v + q - P.c < ρ → ∀ ρ' : ℝ, R P v q ρ' ≤ R P v q ρ) := by sorry

end GDPRDataMarkets.Rights
