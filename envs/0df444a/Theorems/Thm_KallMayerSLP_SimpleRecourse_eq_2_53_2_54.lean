-- Prove2me | Theorems.Thm_KallMayerSLP_SimpleRecourse_eq_2_53_2_54
-- name    : KallMayerSLP.SimpleRecourse.eq_2_53_2_54
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:13:18.733+00:00
-- url     : https://prove2.me/theorems/ad279220-672f-413e-9ef2-0776698f1d00
-- title:
--   (2.53)–(2.54) — Jensen and Edmundson–Madansky bounds for an expected SRT function with bounded support
-- statement:
--   Let $\alpha+\beta\ge0$ and let the support of $\tilde\xi$ be the finite interval $J=\operatorname{supp}\mathbb P_{\tilde\xi}=[a,b]$, with mean $\mu$. Then
--
--   $$
--   \Phi(z)=\varphi(z,\mu)\quad\text{for } z\le a \text{ or } z\ge b, \tag{2.53}
--   $$
--
--   and for $z\in(a,b)$
--
--   $$
--   \varphi(z,\mu)\le\Phi(z)\le\frac{b-\mu}{b-a}\,\varphi(z,a)+\frac{\mu-a}{b-a}\,\varphi(z,b). \tag{2.54}
--   $$
--
--   The lower bound is Jensen's inequality and the upper bound the Edmundson–Madansky inequality, both applied to the convex function $\varphi(z,\cdot)$.
--
--   **Formalization Note** The finite mean follows from the bounded support and is not a separate hypothesis. If $a=b$, (2.54) is vacuous.
--
--   Differences from the source:
--   - encoding: a random variable ξ̃ with distribution ℙ_ξ̃ → a probability measure P on ℝ (the law of ξ̃); reason: every quantity in the statement depends on ξ̃ only through its law; same instances
--   - encoding: J := supp ℙ_ξ̃ = [a, b] → P.support = Set.Icc a b (Mathlib's support of a measure); reason: the same notion: the set of points every neighbourhood of which has positive probability
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, (2.53)–(2.54), p.231 (PDF 240)

import Mathlib
import Definitions.Def_KallMayerSLP_SimpleRecourse_srt
import Definitions.Def_KallMayerSLP_SimpleRecourse_expectedSRT

open MeasureTheory

namespace KallMayerSLP.SimpleRecourse

/-- **(2.53)–(2.54): Jensen and Edmundson–Madansky bounds for an ESRT function on a bounded
support.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, (2.53)–(2.54), p.231 (PDF 240).
Assume `J := supp ℙ_ξ̃ = [a, b]` is a finite interval and `μ = 𝔼_ξ̃[ξ̃]`. Then
`Φ(z) = φ(z, μ)` for `z ≤ a` or `z ≥ b` (2.53), and for `z ∈ (a, b)`
`φ(z, μ) ≤ Φ(z) ≤ ((b − μ)/(b − a)) φ(z, a) + ((μ − a)/(b − a)) φ(z, b)` (2.54).

**Formalization Note.** `P` is the distribution of `ξ̃`; `P.support` is Mathlib's support of a
measure (points all of whose neighbourhoods have positive mass), so `hsupp` is `supp ℙ_ξ̃ = [a, b]`
verbatim. The existence of `μ` (Definition 2.3) follows from the bounded support and is not a
separate hypothesis. If `a = b`, (2.54) is vacuous. -/
theorem eq_2_53_2_54 (α β γ : ℝ) (hαβ : 0 ≤ α + β) (P : Measure ℝ) [IsProbabilityMeasure P]
    (a b : ℝ) (hsupp : P.support = Set.Icc a b) :
    (∀ z : ℝ, z ≤ a ∨ b ≤ z → expectedSRT α β γ P z = srt α β γ z (∫ ξ, ξ ∂P)) ∧
    (∀ z ∈ Set.Ioo a b,
      srt α β γ z (∫ ξ, ξ ∂P) ≤ expectedSRT α β γ P z ∧
        expectedSRT α β γ P z ≤
          (b - ∫ ξ, ξ ∂P) / (b - a) * srt α β γ z a +
            ((∫ ξ, ξ ∂P) - a) / (b - a) * srt α β γ z b) := by sorry

end KallMayerSLP.SimpleRecourse
