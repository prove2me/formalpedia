-- Prove2me | Theorems.Thm_InterimTesting_NotProficient_lemma_A7
-- name    : InterimTesting.NotProficient.lemma_A7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:58.371659+00:00
-- url     : https://prove2.me/theorems/0c378fe7-8735-4a91-af92-8939a42b1e1f
-- title:
--   Lemma A7 a), p. A15 (PDF 41) — under (14), for S0 = N, Pr*[S2 = P] is a four-step function of π with breakpoints 𝒯1(P,0,N), 𝒯1(N,0,N), 𝒯0(N)
-- statement:
--   Suppose (A26) = (14) holds, or the interim assessment is used (where (14) holds automatically). Let $(a,b)=(\phi_{P|P},\phi_{P|N})$ under the formative assessment and $(a,b)=(1,0)$ under the interim assessment. For a school starting not proficient and every $\pi\ge0$, the probability of ending the year proficient under the teachers' optimal response is
--   $$\Pr^*[S_2=P\mid S_0=N]=\begin{cases}\mu B(1+(1-\mu)B),&0\le\pi<\mathcal T_1(P,0,N),\\ \mu\big(B(Aa+B)+(1-\mu B)(Ab+B)\big),&\mathcal T_1(P,0,N)\le\pi<\mathcal T_1(N,0,N),\\ \mu(A+B)(1+(1-\mu)B),&\mathcal T_1(N,0,N)\le\pi<\mathcal T_0(N),\\ \mu(A+B)(1+(1-\mu)(A+B)),&\mathcal T_0(N)\le\pi,\end{cases}$$
--   where $\mathcal T_1(x,0,N)$ is the second-period threshold (11) after observation $x$ with no first-period effort, computed with the accuracy $(a,b)$, and $\mathcal T_0(N)=1/(\mu(1-\mu)A(A+B))$.
--
--   This is the response curve behind the district's choice of incentive.
--
--   **Formalization Note** The page states the formative case; the interim case is the special case $(a,b)=(1,0)$ (p. 12). The hypothesis is `zI = true ∨ Cond14 θ`.
-- source:
--   Virudachalam, Savin & Steinberg, Too Much Information: When Does Additional Testing Benefit Schools?, SSRN 3884543 (version of November 3, 2022), p. A15 (PDF 41), Lemma A7 a), (A89)

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model

namespace InterimTesting.NotProficient

/-- Lemma A7 a), p. A15, (A89): under (A26) (automatic under the interim assessment), for
`S0 = N` the probability `Pr*[S2 = P | S0 = N]` is a four-step function of `π` with breakpoints
`𝒯1(P, 0, N) ≤ 𝒯1(N, 0, N) ≤ 𝒯0(N)`; `(a, b) = acc θ zI` stands for `(ϕ_{P|P}, ϕ_{P|N})`. -/
theorem lemma_A7 (θ : Params) (hθ : θ.Standing) (zI : Bool) (h14 : zI = true ∨ Cond14 θ)
    (π : ℝ) (hπ : 0 ≤ π) :
    PrStar θ zI .N π =
      if π < T1 θ zI .N 0 .P then θ.μ * θ.B * (1 + (1 - θ.μ) * θ.B)
      else if π < T1 θ zI .N 0 .N then
        θ.μ * (θ.B * (θ.A * (acc θ zI).1 + θ.B)
          + (1 - θ.μ * θ.B) * (θ.A * (acc θ zI).2 + θ.B))
      else if π < T0N θ then θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B)
      else θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * (θ.A + θ.B)) := by sorry

end InterimTesting.NotProficient
