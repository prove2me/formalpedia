-- Prove2me | Theorems.Thm_InterimTesting_NotProficient_lemma_A9
-- name    : InterimTesting.NotProficient.lemma_A9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:40.819923+00:00
-- url     : https://prove2.me/theorems/71798798-733e-4fc2-aab7-c33ce6c11bd0
-- title:
--   Lemma A9 a), p. A21 (PDF 47) — for B = 0 and S0 = N, Pr*[S2 = P] is 0, µA, µA(1+(1−µ)A) on three incentive ranges
-- statement:
--   Suppose $B=0$ and the school starts not proficient. Under either assessment decision, for every incentive $\pi\ge0$ the probability of ending the year proficient under the teachers' optimal response is
--   $$\tilde{\Pr}^*[S_2=P\mid S_0=N]=\begin{cases}0,&0\le\pi<\frac1{\mu A},\\ \mu A,&\frac1{\mu A}\le\pi<\tilde{\mathcal T}_0(N),\\ \mu A(1+(1-\mu)A),&\tilde{\mathcal T}_0(N)\le\pi,\end{cases}\qquad\tilde{\mathcal T}_0(N)=\frac1{\mu(1-\mu)A^2}.$$
--
--   This is the response curve the district optimizes over when there is no baseline proficiency.
-- source:
--   Virudachalam, Savin & Steinberg, Too Much Information: When Does Additional Testing Benefit Schools?, SSRN 3884543 (version of November 3, 2022), p. A21 (PDF 47), Lemma A9 a), (A140)

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model

namespace InterimTesting.NotProficient

/-- Lemma A9 a), p. A21, (A140): if `B = 0` and `S0 = N`, then `P̃r*[S2 = P | S0 = N]` is `0`
for `π < 1/(μA)`, `μA` for `1/(μA) ≤ π < 𝒯̃0(N)`, and `μA(1 + (1 − μ)A)` for `π ≥ 𝒯̃0(N)`. -/
theorem lemma_A9 (θ : Params) (hθ : θ.Standing) (hB : θ.B = 0) (zI : Bool) (π : ℝ)
    (hπ : 0 ≤ π) :
    PrStar θ zI .N π =
      if π < 1 / (θ.μ * θ.A) then 0
      else if π < 1 / (θ.μ * (1 - θ.μ) * θ.A ^ 2) then θ.μ * θ.A
      else θ.μ * θ.A * (1 + (1 - θ.μ) * θ.A) := by sorry

end InterimTesting.NotProficient
