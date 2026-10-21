-- Prove2me | Theorems.Thm_InterimTesting_NotProficient_lemma_A11
-- name    : InterimTesting.NotProficient.lemma_A11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:41.521121+00:00
-- url     : https://prove2.me/theorems/4ce5377c-adf3-4b7a-8da7-01d34070411f
-- title:
--   Lemma A11 a), p. A29 (PDF 55) — for B = 0 and S0 = N, the district's optimal probability is 0, µA, µA(1+(1−µ)A) on three budget ranges
-- statement:
--   Suppose $B=0$ and the school starts not proficient. Under either assessment decision $z_I$ and for every budget $M\ge0$, the district's optimal probability that the school ends the year proficient is
--   $$\tilde{\Pr}^*_{z_I}[S_2=P\mid S_0=N]=\begin{cases}0,&0\le M<1,\\ \mu A,&1\le M<1+\frac1{(1-\mu)A},\\ \mu A(1+(1-\mu)A),&1+\frac1{(1-\mu)A}\le M.\end{cases}$$
--
--   Since the right-hand side does not depend on $z_I$, an interim assessment never raises the optimal probability when $B=0$; this is (A210) in the proof of Proposition 1.
--
--   **Formalization Note** The district's optimal probability is `optProb θ zI .N M`, the supremum of $\Pr^*$ over affordable incentives $\pi\ge0$.
-- source:
--   Virudachalam, Savin & Steinberg, Too Much Information: When Does Additional Testing Benefit Schools?, SSRN 3884543 (version of November 3, 2022), p. A29 (PDF 55), Lemma A11 a), (A196); restated as (A210), p. A31 (PDF 57)

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model

namespace InterimTesting.NotProficient

/-- Lemma A11 a), p. A29, (A196) = (A210): if `B = 0` and `S0 = N`, the district`s optimal
probability is `0` for `M < 1`, `μA` for `1 ≤ M < 1 + 1/((1 − μ)A)`, and `μA(1 + (1 − μ)A)`
beyond, with or without the interim assessment. -/
theorem lemma_A11 (θ : Params) (hθ : θ.Standing) (hB : θ.B = 0) (zI : Bool) (M : ℝ)
    (hM : 0 ≤ M) :
    optProb θ zI .N M =
      if M < 1 then 0
      else if M < 1 + 1 / ((1 - θ.μ) * θ.A) then θ.μ * θ.A
      else θ.μ * θ.A * (1 + (1 - θ.μ) * θ.A) := by sorry

end InterimTesting.NotProficient
