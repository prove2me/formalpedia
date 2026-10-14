-- Prove2me | Theorems.Thm_MLLangevin_General_display_28
-- name    : MLLangevin.General.display_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:05.631291+00:00
-- url     : https://prove2.me/theorems/042e0819-fc9a-4415-ab00-6fd02f2bd9c2
-- title:
--   (28), p. 21 — 𝒞(𝒴) ≤ (T₀/γ₀)(1 + (3/2)(2^{(𝔞−1)/2} − 1)⁻¹) if 𝔞 > 1, T₀(1 + (3/2)R)/γ₀ if 𝔞 = 1
-- statement:
--   Let $\mathfrak a\in[1,2]$, $\gamma_0>0$, $T_0>0$ and $R\in\mathbb N$, and set $\gamma_r=\gamma_02^{-r}$ and $T_r=T_02^{-\frac{1+\mathfrak a}2r}$. Then the complexity $\mathcal C(\mathcal Y)=\frac{T_0}{\gamma_0}+\sum_{r=1}^R\big(\frac{T_r}{\gamma_r}+\frac{T_r}{\gamma_{r-1}}\big)$ satisfies
--   $$\mathcal C(\mathcal Y)\le\begin{cases}\dfrac{T_0}{\gamma_0}\Big(1+\tfrac32\big(2^{\frac{\mathfrak a-1}2}-1\big)^{-1}\Big)&\text{if }\mathfrak a>1,\\[2mm] \dfrac{T_0(1+\tfrac32R)}{\gamma_0}&\text{if }\mathfrak a=1.\end{cases}$$
--
--   When $\mathfrak a>1$ the cost of all correcting levels together is of the order of the cost of level $0$; when $\mathfrak a=1$ it grows linearly in $R$.
--
--   **Formalization Note.** The complexity is the formula of p. 6, used for all horizons (the page gives it for horizons that are multiples of the steps). The statement is arithmetic about that formula.
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, (28), p. 21, in Proposition 3.1

import Mathlib
import Definitions.Def_MLLangevin_General_Setting

namespace MLLangevin.General

theorem display_28 (𝔞 γ₀ T₀ : ℝ) (R : ℕ) (h𝔞 : 1 ≤ 𝔞 ∧ 𝔞 ≤ 2) (hγ₀ : 0 < γ₀) (hT₀ : 0 < T₀) :
    cost R γ₀ (geomHorizon T₀ 𝔞)
      ≤ if 1 < 𝔞 then T₀ / γ₀ * (1 + 3 / 2 * ((2 : ℝ) ^ ((𝔞 - 1) / 2) - 1)⁻¹)
        else T₀ * (1 + 3 / 2 * (R : ℝ)) / γ₀ := by sorry

end MLLangevin.General
