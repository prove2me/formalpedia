-- Prove2me | Theorems.Thm_MNLTrisection_Adaptive_lemma_8
-- name    : MNLTrisection.Adaptive.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:46.737644+00:00
-- url     : https://prove2.me/theorems/f1328449-a954-4d3b-9764-ec7a72a9c6e4
-- title:
--   Lemma 8, p. 11 — uniform concentration of sample means with confidence levels δℓ growing with the sample size
-- statement:
--   Let $X_1, \dots, X_L$ be i.i.d. real random variables with mean $\mu$ and $a \le X_i \le b$ almost surely. For every $\delta \in (0,1]$,
--   $$\Pr\Big[\forall \ell \in [L],\ \Big|\frac1\ell\sum_{i=1}^{\ell} X_i - \mu\Big| \le \sqrt{\frac{2(b-a)^2\ln(8/(\delta\ell))}{\ell}}\Big] \ge 1 - L\delta.$$
--
--   Unlike Hoeffding's inequality with a union bound, the effective failure level $\delta\ell$ grows with the sample size, so later confidence intervals are shorter; this is what removes the $\sqrt{\log T}$ factor in Theorem 3.
--
--   **Formalization Note** The sample is $L$ independent copies of a draw from a probability measure $D$, observed through a measurable $X : \Omega \to \mathbb R$ (the encoding of the platform's Hoeffding inequality, `UnderstandingML.hoeffding_inequality`), and $\mu = \int X\,dD$. The probability is the product measure of the event. When $\delta\ell > 8$ the logarithm is negative and the square root is $0$ in Lean; this happens only when $L\delta > 8$, where the bound $1 - L\delta < 0$ is void. The page's "for all $\ell \in [L]$" in the hypothesis is a typo for $i$.
-- source:
--   Chen, Wang & Zhou, An Optimal Policy for Dynamic Assortment Planning Under Uncapacitated Multinomial Logit Models, arXiv:1805.04785v2, p. 11, Lemma 8, Eq. (11)

import Mathlib
import Definitions.Def_UnderstandingML_Framework
import Definitions.Def_MNLTrisection_Adaptive_Model

namespace MNLTrisection.Adaptive

open MeasureTheory UnderstandingML

/-- **Lemma 8** (p. 11). Let `X₁, …, X_L` be i.i.d. with mean `μ` and `a ≤ X_i ≤ b` almost
surely. For any `δ ∈ (0, 1]`,
`Pr[∀ ℓ ∈ [L], |(1/ℓ) ∑_{i=1}^ℓ X_i − μ| ≤ √(2(b − a)² ln(8/(δℓ))/ℓ)] ≥ 1 − Lδ`.
The sample is the product law of `L` copies of a distribution `D`, observed through a measurable
`X : Ω → ℝ`; `μ = ∫ X dD`. -/
theorem lemma_8 {Ω : Type*} [MeasurableSpace Ω] (D : Measure Ω) [IsProbabilityMeasure D]
    (X : Ω → ℝ) (hX : Measurable X) {a b : ℝ} (hab : ∀ᵐ ω ∂D, a ≤ X ω ∧ X ω ≤ b)
    (L : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ENNReal.ofReal (1 - L * δ) ≤
      iidLaw D L {ω | ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ L →
        |(∑ i ∈ Finset.univ.filter (fun i : Fin L => (i : ℕ) < ℓ), X (ω i)) / ℓ - ∫ x, X x ∂D| ≤
          Real.sqrt (2 * (b - a) ^ 2 * Real.log (8 / (δ * ℓ)) / ℓ)} := by sorry

end MNLTrisection.Adaptive
