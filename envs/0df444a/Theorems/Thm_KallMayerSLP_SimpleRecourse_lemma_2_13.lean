-- Prove2me | Theorems.Thm_KallMayerSLP_SimpleRecourse_lemma_2_13
-- name    : KallMayerSLP.SimpleRecourse.lemma_2_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:13:12.74731+00:00
-- url     : https://prove2.me/theorems/fea2cb9b-ec9e-4815-b27e-e2f7d7f8b602
-- title:
--   Lemma 2.13 — the conditional expected SRT function is exact outside its interval
-- statement:
--   Let $\alpha+\beta\ge0$, let $\tilde\xi$ have law $\mathbb P_{\tilde\xi}$ with finite mean, and let $I=(a,b]$ with $\mathbb P_{\tilde\xi}(I)>0$, where $a$ and/or $b$ is finite. With $\mu_{|I}$ and $\Phi_{|I}$ as in Lemma 2.12,
--
--   $$
--   \Phi_{|I}(z)=\varphi(z,\mu_{|I})\quad\text{for } z\le a,\qquad \Phi_{|I}(z)=\varphi(z,\mu_{|I})\quad\text{for } z\ge b.
--   $$
--
--   Outside the interval the conditional expected SRT function equals its Jensen lower bound. This makes the partition bounds of Lemmas 2.14 and 2.16 exact at the partition points.
--
--   **Formalization Note** For $a=-\infty$ the first clause is vacuous, and for $b=+\infty$ the second.
--
--   Differences from the source:
--   - encoding: a random variable ξ̃ with distribution ℙ_ξ̃ → a probability measure P on ℝ (the law of ξ̃); reason: every quantity in the statement depends on ξ̃ only through its law; same instances
--   - encoding: 𝔼_ξ̃[ξ̃] provided to exist (Definition 2.3) → Integrable (fun ξ => ξ) P; reason: existence of a finite mean is integrability of the identity under the law
--   - encoding: conditional expectations 𝔼_ξ̃[· | ξ ∈ I] and p_ν = ℙ_ξ̃(I_ν) → integrals against the conditional law P[|I] = ℙ(I)⁻¹·P|_I, and P.real I; reason: the elementary conditional expectation given an event of positive probability; same instances
--   - encoding: interval I = {ξ | a < ξ ≤ b} with a, b ∈ [−∞, +∞] → a b : EReal and I = {ξ : ℝ | a < ξ ∧ ξ ≤ b}; reason: extended-real bounds express a = −∞ or b = +∞ directly; same intervals
--   - generalization: I ⊊ supp ℙ_ξ̃, implying at least one of a, b finite (standing assumption before Lemma 2.12) → not assumed (a = −∞ and b = +∞ together are allowed); reason: the conclusion holds for every interval of positive probability; with the assumption added it is the printed lemma
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Lemma 2.13, p.230 (PDF 239)

import Mathlib
import Definitions.Def_KallMayerSLP_SimpleRecourse_srt
import Definitions.Def_KallMayerSLP_SimpleRecourse_expectedSRT

open MeasureTheory ProbabilityTheory

namespace KallMayerSLP.SimpleRecourse

/-- **Lemma 2.13 (the conditional ESRT function is exact outside its interval).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Lemma 2.13, p.230 (PDF 239).
For any finite `a` and/or `b`, for `I = (a, b]` (with `ℙ_ξ̃(I) > 0`) holds
`Φ_{|I}(z) = φ(z, μ_{|I})` for `z ≤ a`, and `Φ_{|I}(z) = φ(z, μ_{|I})` for `z ≥ b`.

**Formalization Note.** As in Lemma 2.12: `a, b` are extended reals, `I = {ξ ∈ ℝ | a < ξ ≤ b}`,
`ℙ_ξ̃(I) > 0` (the standing assumption before Lemma 2.12), `μ_{|I} = ∫ ξ dP[|I]`,
`Φ_{|I} = expectedSRT α β γ P[|I]`. "For finite `a`" is automatic: for `a = −∞` there is no real
`z ≤ a`, and for `b = +∞` no real `z ≥ b`. `I ⊊ supp ℙ_ξ̃` is not assumed. -/
theorem lemma_2_13 (α β γ : ℝ) (hαβ : 0 ≤ α + β) (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : Integrable (fun ξ => ξ) P) (a b : EReal)
    (hI : 0 < P {ξ : ℝ | a < (ξ : EReal) ∧ (ξ : EReal) ≤ b}) :
    (∀ z : ℝ, (z : EReal) ≤ a →
      expectedSRT α β γ P[|{ξ : ℝ | a < (ξ : EReal) ∧ (ξ : EReal) ≤ b}] z =
        srt α β γ z (∫ ξ, ξ ∂P[|{ξ : ℝ | a < (ξ : EReal) ∧ (ξ : EReal) ≤ b}])) ∧
    (∀ z : ℝ, b ≤ (z : EReal) →
      expectedSRT α β γ P[|{ξ : ℝ | a < (ξ : EReal) ∧ (ξ : EReal) ≤ b}] z =
        srt α β γ z (∫ ξ, ξ ∂P[|{ξ : ℝ | a < (ξ : EReal) ∧ (ξ : EReal) ≤ b}])) := by sorry

end KallMayerSLP.SimpleRecourse
