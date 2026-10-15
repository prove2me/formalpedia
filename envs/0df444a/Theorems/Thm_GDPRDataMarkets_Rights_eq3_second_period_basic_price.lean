-- Prove2me | Theorems.Thm_GDPRDataMarkets_Rights_eq3_second_period_basic_price
-- name    : GDPRDataMarkets.Rights.eq3_second_period_basic_price
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:09.401151+00:00
-- url     : https://prove2.me/theorems/4d360146-c08c-4dd9-86cd-2124b66fd1c9
-- title:
--   Eq. (3), p. 14 — the second-period basic price is p*_2M(p₁) = 1/2 if v*_M(p₁) ≥ 1/√2 and 1 otherwise
-- statement:
--   Let $w\in[0,1]$ be the opt-in threshold $v^*_M(p_1)$, so that the consumers in $[w,1]$ have opted in and those in $[0,w)$ have not. Let
--   $$\pi_2(w,p_2)=\int_w^1 r^*_M(v,p_2)\,dv+p_2\cdot\big|\{v\in[0,w): v\ge p_2\}\big|,\qquad r^*_M(v,p_2)=(\mu-\sigma)v+\min\{v,p_2\}-c,$$
--   be the firm's second-period profit at basic price $p_2$. Then:
--
--   1. for $p_2\in[0,1]$,
--   $$\pi_2(w,p_2)=p_2-\tfrac12p_2^2-\tfrac12\min\{w,p_2\}^2+\tfrac{\mu-\sigma}{2}(1-w^2)-(1-w)c;$$
--   2. if $w\ge1/\sqrt2$, then $p_2=1/2$ maximizes $\pi_2(w,\cdot)$ over all real $p_2$;
--   3. if $w<1/\sqrt2$, then $p_2=1$ maximizes $\pi_2(w,\cdot)$ over all real $p_2$.
--
--   Hence
--   $$p^*_{2M}(p_1)=\begin{cases}1/2, & v^*_M(p_1)\ge 1/\sqrt2,\\ 1, & \text{otherwise.}\end{cases}$$
--   When few consumers opted out, the firm prefers not to sell the basic good at all (price $1$) to avoid cannibalizing the personalized good.
--
--   **Formalization Note** At $w=1/\sqrt2$ both prices are optimal; the statement asserts optimality, not uniqueness. Prices $p_2\ge1$ all yield the same profit; the theorem names $p_2=1$ as the paper does.
-- source:
--   Ke, Sudhir, Privacy Rights and Data Security: GDPR and Personal Data Markets, SSRN 3643979 (pdfTeX build 2022-09-14), p. 14, eq. (3) and the display before it

import Mathlib
import Definitions.Def_GDPRDataMarkets_Rights_Model
import Definitions.Def_GDPRDataMarkets_Rights_ClosedForms

namespace GDPRDataMarkets.Rights

/-- Eq. (3), p. 14: with opt-in threshold `w = v*_M(p₁) ∈ [0, 1]`, the second-period objective is
`p₂ − p₂²/2 − min{w, p₂}²/2 + ((μ − σ)/2)(1 − w²) − (1 − w)c` for `p₂ ∈ [0, 1]`, and it is maximized
over all real `p₂` at `p₂ = 1/2` if `w ≥ 1/√2` and at `p₂ = 1` otherwise. -/
theorem eq3_second_period_basic_price (P : Params) (w : ℝ) (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    (∀ q ∈ Set.Icc (0 : ℝ) 1, profit2Red P w q
        = q - q ^ 2 / 2 - (min w q) ^ 2 / 2 + (P.mu - P.sigma) / 2 * (1 - w ^ 2) - (1 - w) * P.c) ∧
    (1 / Real.sqrt 2 ≤ w → ∀ q : ℝ, profit2Red P w q ≤ profit2Red P w (1 / 2)) ∧
    (w < 1 / Real.sqrt 2 → ∀ q : ℝ, profit2Red P w q ≤ profit2Red P w 1) := by sorry

end GDPRDataMarkets.Rights
