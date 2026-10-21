-- Prove2me | Theorems.Thm_InterimTesting_NotProficient_lemma_A10
-- name    : InterimTesting.NotProficient.lemma_A10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:36.06535+00:00
-- url     : https://prove2.me/theorems/47569835-c89d-4fdd-b1f4-0f77a1e6e7de
-- title:
--   Lemma A10 a), p. A25 (PDF 51) — for B = 0 and S0 = N, the optimal incentive is 0, 1/(µA), 1/(µ(1−µ)A²) on three budget ranges
-- statement:
--   Suppose $B=0$ and the school starts not proficient. Under either assessment decision and for every budget $M\ge0$, the least optimal merit-based incentive of the district's problem (9)–(10) is
--   $$\tilde\pi^*=\begin{cases}0,&0\le M<1,\\ \frac1{\mu A},&1\le M<1+\frac1{(1-\mu)A},\\ \frac1{\mu(1-\mu)A^2},&1+\frac1{(1-\mu)A}\le M.\end{cases}$$
--
--   The budget breakpoints are exactly the expected payments $\pi\,\tilde{\Pr}^*$ at the two effort thresholds.
--
--   **Formalization Note** An incentive is optimal if $\pi\ge0$, $\pi\Pr^*(\pi)\le M$ and $\Pr^*(\pi)$ equals the district's optimal value; the statement is that $\tilde\pi^*$ is the least such incentive (`IsLeast`).
-- source:
--   Virudachalam, Savin & Steinberg, Too Much Information: When Does Additional Testing Benefit Schools?, SSRN 3884543 (version of November 3, 2022), p. A25 (PDF 51), Lemma A10 a), (A171)

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model

namespace InterimTesting.NotProficient

/-- Lemma A10 a), p. A25, (A171): if `B = 0` and `S0 = N`, the least optimal incentive is `0`
for `M < 1`, `1/(μA)` for `1 ≤ M < 1 + 1/((1 − μ)A)`, and `1/(μ(1 − μ)A²)` beyond. -/
theorem lemma_A10 (θ : Params) (hθ : θ.Standing) (hB : θ.B = 0) (zI : Bool) (M : ℝ)
    (hM : 0 ≤ M) :
    IsLeast {π | IsOptIncentive θ zI .N M π}
      (if M < 1 then 0
       else if M < 1 + 1 / ((1 - θ.μ) * θ.A) then 1 / (θ.μ * θ.A)
       else 1 / (θ.μ * (1 - θ.μ) * θ.A ^ 2)) := by sorry

end InterimTesting.NotProficient
