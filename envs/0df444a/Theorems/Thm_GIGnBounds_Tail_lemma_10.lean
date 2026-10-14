-- Prove2me | Theorems.Thm_GIGnBounds_Tail_lemma_10
-- name    : GIGnBounds.Tail.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:48.091285+00:00
-- url     : https://prove2.me/theorems/b92e30d0-5bcd-4859-af0e-252ef9c34d94
-- title:
--   Lemma 10 — $\theta=(1-c)/(11c\,E[Z_1^2])$ is admissible in Lemma 9
-- statement:
--   Let $Z_1$ be a nonnegative random variable with law $\nu$, $\mathbb E[Z_1]=1$ and $\mathbb E[Z_1^2]<\infty$, and let $c\in(0,1)$.
--
--   **Lemma 10.**
--
--   $$\mathbb E\Big[\exp\Big(\frac{1-c}{11c\,\mathbb E[Z_1^2]}(c-Z_1)\Big)\Big]\le1.$$
--
--   That is, one can take $\theta=\frac{1-c}{11c\,\mathbb E[Z_1^2]}$ in Lemma 9, an explicit exponent in terms of $c$ and the first two moments of $Z_1$.
--
--   **Formalization Note.** Only the law of $Z_1$ matters, so the statement is about $\nu$. The paper's "same assumptions as Lemma 9" are taken to be: nonnegative, mean $1$, $c\in(0,1)$ (the hypothesis on $\theta$ in Lemma 9 is what this lemma supplies).
-- source:
--   Li and Goldberg, Simple and explicit bounds for multi-server queues with 1/(1−ρ) scaling, arXiv:1706.04628v3, p. 33, Lemma 10

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting

open MeasureTheory ProbabilityTheory

namespace GIGnBounds.Tail

/-- **Lemma 10** (Li–Goldberg, arXiv:1706.04628v3, p. 33). Let `Z₁` be nonnegative with `E[Z₁] = 1` and
`E[Z₁²] < ∞`, and `c ∈ (0, 1)`. Then `E[exp(((1 − c)/(11 c E[Z₁²])) (c − Z₁))] ≤ 1`; that is,
`θ = (1 − c)/(11 c E[Z₁²])` is admissible in Lemma 9. Stated for the law `ν` of `Z₁`. -/
theorem lemma_10 (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iio 0) = 0)
    (hν1 : ∫ z, z ∂ν = 1) (hν2 : ∫⁻ z, ENNReal.ofReal (z ^ 2) ∂ν < ⊤)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ∫ z, Real.exp ((1 - c) / (11 * c * ∫ w, w ^ 2 ∂ν) * (c - z)) ∂ν ≤ 1 := by sorry

end GIGnBounds.Tail
