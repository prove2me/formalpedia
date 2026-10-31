-- Prove2me | Theorems.Thm_KallMayerSLP_SimpleRecourse_lemma_2_12
-- name    : KallMayerSLP.SimpleRecourse.lemma_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:13:18.519433+00:00
-- url     : https://prove2.me/theorems/7f403425-e325-408a-b344-dbfdcacce525
-- title:
--   Lemma 2.12 — Jensen's inequality for the conditional expected SRT function
-- statement:
--   Let $\alpha+\beta\ge0$, let $\tilde\xi$ have law $\mathbb P_{\tilde\xi}$ with finite mean, and let $I=\{\xi\mid a<\xi\le b\}$ ($-\infty\le a$, $b\le+\infty$) with $\mathbb P_{\tilde\xi}(I)>0$. Write $\mu_{|I}=\mathbb E_{\tilde\xi}[\tilde\xi\mid\xi\in I]$ and $\Phi_{|I}(z)=\mathbb E_{\tilde\xi}[\varphi(z,\tilde\xi)\mid\xi\in I]$. Then for all $z\in\mathbb R$
--
--   $$
--   \varphi(z,\mu_{|I})\le\Phi_{|I}(z)=\frac{1}{\mathbb P_{\tilde\xi}(I)}\int_a^b\varphi(z,\xi)\,dF_{\tilde\xi}(\xi).
--   $$
--
--   This is the conditional form of the Jensen lower bound, the building block of the partition bounds of Lemmas 2.14–2.16.
--
--   **Formalization Note** $\int_a^b\dots dF_{\tilde\xi}$ is the integral over $I=(a,b]$.
--
--   Differences from the source:
--   - encoding: a random variable ξ̃ with distribution ℙ_ξ̃ → a probability measure P on ℝ (the law of ξ̃); reason: every quantity in the statement depends on ξ̃ only through its law; same instances
--   - encoding: 𝔼_ξ̃[ξ̃] provided to exist (Definition 2.3) → Integrable (fun ξ => ξ) P; reason: existence of a finite mean is integrability of the identity under the law
--   - encoding: conditional expectations 𝔼_ξ̃[· | ξ ∈ I] and p_ν = ℙ_ξ̃(I_ν) → integrals against the conditional law P[|I] = ℙ(I)⁻¹·P|_I, and P.real I; reason: the elementary conditional expectation given an event of positive probability; same instances
--   - encoding: interval I = {ξ | a < ξ ≤ b} with a, b ∈ [−∞, +∞] → a b : EReal and I = {ξ : ℝ | a < ξ ∧ ξ ≤ b}; reason: extended-real bounds express a = −∞ or b = +∞ directly; same intervals
--   - generalization: I ⊊ supp ℙ_ξ̃, implying at least one of a, b finite (standing assumption before Lemma 2.12) → not assumed (a = −∞ and b = +∞ together are allowed); reason: the conclusion holds for every interval of positive probability; with the assumption added it is the printed lemma
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Lemma 2.12, p.230 (PDF 239)

import Mathlib
import Definitions.Def_KallMayerSLP_SimpleRecourse_srt
import Definitions.Def_KallMayerSLP_SimpleRecourse_expectedSRT

open MeasureTheory ProbabilityTheory

namespace KallMayerSLP.SimpleRecourse

/-- **Lemma 2.12 (conditional Jensen inequality for SRT functions).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Lemma 2.12, p.230 (PDF 239).
For an interval `I = {ξ | a < ξ ≤ b}` with `ℙ_ξ̃(I) > 0`, with `μ_{|I} = 𝔼_ξ̃[ξ̃ | ξ ∈ I]` and
`Φ_{|I}(z) = 𝔼_ξ̃[φ(z, ξ̃) | ξ ∈ I]`, for all `z ∈ ℝ`
`φ(z, μ_{|I}) ≤ Φ_{|I}(z) = (1/ℙ_ξ̃(I)) ∫_a^b φ(z, ξ) dF_ξ̃(ξ)`.

**Formalization Note.** `P` is the distribution of `ξ̃`, `hP` the existence of `𝔼_ξ̃[ξ̃]`
(Definition 2.3). The bounds `a, b` are extended reals (`a = −∞` or `b = +∞` allowed), and
`I = {ξ ∈ ℝ | a < ξ ≤ b}`. The conditional law is `P[|I] = ℙ_ξ̃(I)⁻¹ · P|_I`, so
`μ_{|I} = ∫ ξ dP[|I]` and `Φ_{|I} = expectedSRT α β γ P[|I]`; `∫_a^b … dF_ξ̃` is the integral over
`I = (a, b]`. The book also requires `I ⊊ supp ℙ_ξ̃`; that is not needed and not assumed. -/
theorem lemma_2_12 (α β γ : ℝ) (hαβ : 0 ≤ α + β) (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : Integrable (fun ξ => ξ) P) (a b : EReal)
    (hI : 0 < P {ξ : ℝ | a < (ξ : EReal) ∧ (ξ : EReal) ≤ b}) (z : ℝ) :
    srt α β γ z (∫ ξ, ξ ∂P[|{ξ : ℝ | a < (ξ : EReal) ∧ (ξ : EReal) ≤ b}]) ≤
        expectedSRT α β γ P[|{ξ : ℝ | a < (ξ : EReal) ∧ (ξ : EReal) ≤ b}] z ∧
      expectedSRT α β γ P[|{ξ : ℝ | a < (ξ : EReal) ∧ (ξ : EReal) ≤ b}] z =
        (P.real {ξ : ℝ | a < (ξ : EReal) ∧ (ξ : EReal) ≤ b})⁻¹ *
          ∫ ξ in {ξ : ℝ | a < (ξ : EReal) ∧ (ξ : EReal) ≤ b}, srt α β γ z ξ ∂P := by sorry

end KallMayerSLP.SimpleRecourse
