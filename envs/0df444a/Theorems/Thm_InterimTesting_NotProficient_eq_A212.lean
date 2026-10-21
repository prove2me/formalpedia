-- Prove2me | Theorems.Thm_InterimTesting_NotProficient_eq_A212
-- name    : InterimTesting.NotProficient.eq_A212
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:37.409807+00:00
-- url     : https://prove2.me/theorems/cb2e0542-0702-45e1-905e-d2e32566e154
-- title:
--   (A212)–(A213), p. A32 (PDF 58) — for B > 0, the interim-assessment optimal probability is a four-step function of M with breakpoints ℋ^I_1, ℋ^I_2, M_U
-- statement:
--   Suppose $B>0$ and the school starts not proficient. With the (free) interim assessment, for every budget $M\ge0$ the district's optimal probability that the school ends the year proficient is
--   $$\Pr\nolimits^*_{1}[S_2=P\mid S_0=N]=\begin{cases}\mu B(1+(1-\mu)B),&0\le M<\mathcal H^I_1(\mu),\\ \mu B\big((A+B)+(1-\mu B)\big),&\mathcal H^I_1(\mu)\le M<\mathcal H^I_2(\mu),\\ \mu(A+B)(1+(1-\mu)B),&\mathcal H^I_2(\mu)\le M<M_U,\\ \mu(A+B)(1+(1-\mu)(A+B)),&M_U\le M,\end{cases}$$
--   where $\mathcal H^I_1(\mu)=\mu B\frac{A+1+(1-\mu)B}{A}$ (A200), $\mathcal H^I_2(\mu)=\frac{(A+B)(1+(1-\mu)B)}{A}$ (A213) and $M_U=\frac{1+(1-\mu)B}{(1-\mu)A}+1$.
--
--   This is the second value curve Proposition 1 compares.
--
--   **Formalization Note** The page derives (A212) inside the proof of Proposition 1, where (A26) is assumed; under the interim assessment the condition holds automatically, so it is not a hypothesis here.
-- source:
--   Virudachalam, Savin & Steinberg, Too Much Information: When Does Additional Testing Benefit Schools?, SSRN 3884543 (version of November 3, 2022), p. A32 (PDF 58), (A212)–(A213), proof of Proposition 1; (A200), p. A30 (PDF 56)

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model

namespace InterimTesting.NotProficient

/-- (A212)–(A213), p. A32: for `B > 0`, the optimal probability under the interim assessment is a
four-step function of the budget `M` with breakpoints `ℋ^I_1(μ)`, `ℋ^I_2(μ)`, `M_U`. -/
theorem eq_A212 (θ : Params) (hθ : θ.Standing) (hB : 0 < θ.B) (M : ℝ) (hM : 0 ≤ M) :
    optProb θ true .N M =
      if M < HI1 θ then θ.μ * θ.B * (1 + (1 - θ.μ) * θ.B)
      else if M < HI2 θ then θ.μ * θ.B * ((θ.A + θ.B) + (1 - θ.μ * θ.B))
      else if M < MU θ then θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B)
      else θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * (θ.A + θ.B)) := by sorry

end InterimTesting.NotProficient
