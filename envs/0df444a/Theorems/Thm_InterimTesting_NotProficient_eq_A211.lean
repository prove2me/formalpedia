-- Prove2me | Theorems.Thm_InterimTesting_NotProficient_eq_A211
-- name    : InterimTesting.NotProficient.eq_A211
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:41.311272+00:00
-- url     : https://prove2.me/theorems/472a42de-a912-414f-9abb-2d76a4c84e12
-- title:
--   (A211), proof of Proposition 1, p. A31 (PDF 57) — for B > 0 under (14), the formative-only optimal probability is a four-step function of M
-- statement:
--   Suppose $B>0$ and condition (14) holds, and the school starts not proficient. First, $\mathcal H_1(\mu)$ of (15) equals its form (A154),
--   $$\mathcal H_1(\mu)=\mu\big(B(A\phi_{P|P}+B)+(1-\mu B)(A\phi_{P|N}+B)\big)\,\mathcal T_1(P,0,N).$$
--   Second, without the interim assessment, for every budget $M\ge0$ the district's optimal probability that the school ends the year proficient is
--   $$\Pr\nolimits^*_{0}[S_2=P\mid S_0=N]=\begin{cases}\mu B(1+(1-\mu)B),&0\le M<\mathcal H_1(\mu),\\ \mu\big(B(A\phi_{P|P}+B)+(1-\mu B)(A\phi_{P|N}+B)\big),&\mathcal H_1(\mu)\le M<\mathcal H_2(\mu),\\ \mu(A+B)(1+(1-\mu)B),&\mathcal H_2(\mu)\le M<M_U,\\ \mu(A+B)(1+(1-\mu)(A+B)),&M_U\le M,\end{cases}$$
--   where $M_U=\frac{1+(1-\mu)B}{(1-\mu)A}+1$ and $\mathcal H_2(\mu)=\mu(A+B)(1+(1-\mu)B)\,\mathcal T_1(N,0,N)$ (A155).
--
--   This is one of the two value curves Proposition 1 compares.
-- source:
--   Virudachalam, Savin & Steinberg, Too Much Information: When Does Additional Testing Benefit Schools?, SSRN 3884543 (version of November 3, 2022), p. A31 (PDF 57), (A211), proof of Proposition 1; (A154)–(A155), p. A23 (PDF 49)

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model

namespace InterimTesting.NotProficient

/-- (A211), proof of Proposition 1, p. A31: for `B > 0` under (14), the optimal probability
without the interim assessment is a four-step function of the budget `M` with breakpoints
`ℋ1(μ)`, `ℋ2(μ)`, `M_U`; also `ℋ1` of (15) agrees with its form (A154). -/
theorem eq_A211 (θ : Params) (hθ : θ.Standing) (hB : 0 < θ.B) (h14 : Cond14 θ) :
    H1 θ = θ.μ * (θ.B * (θ.A * θ.φPP + θ.B) + (1 - θ.μ * θ.B) * (θ.A * θ.φPN + θ.B))
        * T1 θ false .N 0 .P ∧
      ∀ M : ℝ, 0 ≤ M →
        optProb θ false .N M =
          if M < H1 θ then θ.μ * θ.B * (1 + (1 - θ.μ) * θ.B)
          else if M < H2 θ then
            θ.μ * (θ.B * (θ.A * θ.φPP + θ.B) + (1 - θ.μ * θ.B) * (θ.A * θ.φPN + θ.B))
          else if M < MU θ then θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B)
          else θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * (θ.A + θ.B)) := by sorry

end InterimTesting.NotProficient
