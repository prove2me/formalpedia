-- Prove2me | Theorems.Thm_MaxCutMatrix2027_Upper_multiplicative_chernoff
-- name    : MaxCutMatrix2027.Upper.multiplicative_chernoff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T12:47:21.31108+00:00
-- url     : https://prove2.me/theorems/e7c47ec5-179c-45a7-a0e5-13bf3f8c3a67
-- title:
--   Proposition 3.4 — Full bounded-variable multiplicative Chernoff bound
-- statement:
--   Let $X_1,\ldots,X_m$ be independent real random variables on an arbitrary probability space, with $0\le X_i\le1$ almost surely. Put $S=\sum_i X_i$ and $\mu=\mathbb E S>0$. For every real $\delta>0$,
--   $$\Pr\{S\ge(1+\delta)\mu\}\le\exp\left(-\frac{\delta^2\mu}{2+\delta}\right).$$
--   The variables need not be Bernoulli, identically distributed or finite-valued, and there is no upper restriction on the deviation parameter. Measurability is the standard meaning of random variable. The almost-sure bounds imply integrability on the probability space, so no default integral value is used. This gives the sample-overflow tail bound without narrowing the proposition to that application.
--
--   Differences from the source:
--   - encoding: independent random variables and their probability → measurable functions on an arbitrary probability space, iIndepFun, and the real value of the finite event measure; reason: these are the standard measurable-random-variable convention and the identical probability law
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), Proposition 3.4, p.16 (PDF p.16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MaxCutMatrix2027.Upper

/-- Proposition 3.4, p.16. Arbitrary independent bounded real random variables;
all positive deviations, exact denominator 2+δ. -/
theorem multiplicative_chernoff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ) (X : Fin m → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : 0 < ∫ ω, ∑ i, X i ω ∂μ) (δ : ℝ) (hδ : 0 < δ) :
    μ.real {ω | (1 + δ) * (∫ z, ∑ i, X i z ∂μ) ≤ ∑ i, X i ω} ≤
      Real.exp (-(δ ^ 2 * (∫ z, ∑ i, X i z ∂μ)) / (2 + δ)) := by sorry

end MaxCutMatrix2027.Upper
