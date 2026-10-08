-- Prove2me | Theorems.Thm_LariviereIGFR_Moments_nthMoment_lt_top_iff_tail
-- name    : LariviereIGFR.Moments.nthMoment_lt_top_iff_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:55.537178+00:00
-- url     : https://prove2.me/theorems/7b44881f-91c2-4548-b7ec-3f742e57a571
-- title:
--   Proof of Theorem 2, p. 603 — E[Xⁿ] is finite iff its part over {X > y} is finite
-- statement:
--   Let $X$ be a nonnegative random variable with law $\mu$ (a probability measure with $\mu((-\infty,0))=0$), let $y\in\mathbb R$ and let $n>0$ be real. Then
--   $$
--   \mathbb E[X^n]<\infty\iff \int_{(y,\infty)}x^n\,d\mu(x)<\infty .
--   $$
--
--   In the paper this is the decomposition $\mathbb E[X^n]=\mathbb E[X^n\mid X\le y]\Phi(y)+\mathbb E[X^n\mid X>y]\bar\Phi(y)$ together with the remark that the first term is finite; it reduces finiteness of a moment to the tail beyond any fixed level.
--
--   **Formalization Note** The paper justifies finiteness of the first term by "$\mathbb E[X^n\mid X\le y]<y^{n+1}$", which is false for $y<1$ (the correct bound is $y^n$); only the finiteness is used and only the finiteness is stated here. No density is needed.
-- source:
--   Lariviere, A note on probability distributions with increasing generalized failure rates, Oper. Res. 54(3) (2006), p. 603, §3, proof of Theorem 2, first paragraph

import Mathlib
import Definitions.Def_LariviereIGFR_Moments_Setting

namespace LariviereIGFR.Moments

open MeasureTheory ProbabilityTheory

/-- Proof of Theorem 2, p. 603: for a nonnegative random variable, `𝔼[Xⁿ]` is finite iff its part
`𝔼[Xⁿ; X > y]` over `{X > y}` is finite (the part over `{X ≤ y}` is always finite). -/
theorem nthMoment_lt_top_iff_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnn : μ (Set.Iio 0) = 0) (y : ℝ) (n : ℝ) (hn : 0 < n) :
    nthMoment μ n < ⊤ ↔ (∫⁻ x in Set.Ioi y, ENNReal.ofReal (x ^ n) ∂μ) < ⊤ := by sorry

end LariviereIGFR.Moments
