-- Prove2me | Theorems.Thm_LefebvreVariations_azuma_hoeffding_single_step
-- name    : LefebvreVariations.azuma_hoeffding_single_step
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:27:22.464794+00:00
-- url     : https://prove2.me/theorems/d2de45cf-41b5-5710-91c1-1f54deb0a7c2
-- title:
--   Lefebvre's variations, No. 168 — on a theme by Asi, Feldman, Kale, Koren, Singhal and Talwar: the one-step Azuma-Hoeffding inequality for a conditionally bounded variable
-- statement:
--   Let $\mathcal F_0\subseteq\mathcal F_1$ be $\sigma$-algebras, $X$ an $\mathcal F_1$-measurable variable with $a\le X\le b$ almost surely, and $\lambda>0$. If $\mathbb{E}[X\mid\mathcal F_0]\le\mu$ almost surely, then
--   $$\mathbb{P}(X\ge\mu+\lambda)\le \exp\!\Bigl(-\frac{2\lambda^2}{(b-a)^2}\Bigr),$$
--   and if $\mathbb{E}[X\mid\mathcal F_0]\ge\mu$ almost surely, then $\mathbb{P}(X\le\mu-\lambda)\le \exp\!\bigl(-2\lambda^2/(b-a)^2\bigr)$.
--
--   This is the one-step (conditional Hoeffding) case of the Azuma--Hoeffding inequality for sums of bounded variables with conditionally bounded means.
--
--   **Formalization Note** The statement is that of `FewExperts.lemma_1_azuma_hoeffding` (both tails) with the hypothesis `n = 1` added, so the sums over `Finset.Icc 1 n` have the single term `t = 1` and the conditioning is on `ℱ 0`. `ℱ : Filtration ℕ mΩ` is any filtration to which `X` is (strongly) adapted; `a 1 ≤ X 1 ≤ b 1` holds almost surely; probabilities are bounded as measures (`P {…} ≤ ENNReal.ofReal …`); `lam` stands for `λ`. If `b 1 = a 1` the right-hand side is `exp 0 = 1` by Lean's convention `x / 0 = 0`, so the bound is trivial there.
--
--   **Why this is a variation.** Variation of the open platform problem FewExperts.lemma_1_azuma_hoeffding (Azuma-Hoeffding for n variables with conditionally bounded means). It is the case n=1 in the parent's own statement, i.e. the conditional Hoeffding lemma, the key step from which the general case is obtained by iterating conditional expectations; it is the parent with n=1 substituted, so a consequence of the parent. The Proved platform theorems checked (azuma_hoeffding_two_sided, Concentration.hoeffding_two_sided) have different hypotheses (sub-Gaussian conditional MGF; independence) and a factor 2, so they do not directly give this one-sided bound.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent: FewExperts.lemma_1_azuma_hoeffding (platform, Open), Lemma 1 of Asi, Feldman, Kale, Koren, Singhal and Talwar, A Few Experts Suffice (manuscript, STOC 2027 submission, as given in the parent's source field; not re-checked), itself citing Cesa-Bianchi and Lugosi, Prediction, Learning, and Games (2006), Lemma A.7 (cited from memory). The one-step case is the conditional form of Hoeffding's lemma, from W. Hoeffding, Probability inequalities for sums of bounded random variables, J. Amer. Statist. Assoc. 58 (1963) 13-30 (reference verified online; the precise equation number was not checked). Degenerate cases: b=a gives right-hand side exp(0)=1 in Lean (x/0=0); b<a makes the almost-sure hypothesis contradictory on a probability space.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

open MeasureTheory ProbabilityTheory

/-- The one-step case `n = 1` of `FewExperts.lemma_1_azuma_hoeffding`: Hoeffding's lemma in conditional form. If
`a ≤ X₁ ≤ b` almost surely and `E[X₁ | ℱ₀] ≤ μ`, then `P(X₁ ≥ μ + λ) ≤ exp(-2λ²/(b-a)²)`, and symmetrically for the lower tail.
Source: W. Hoeffding, *Probability inequalities for sums of bounded random variables*, J. Amer. Statist. Assoc. 58 (1963) (cited from memory);
Cesa-Bianchi–Lugosi, *Prediction, Learning, and Games*, Lemma A.7 (cited from memory). -/
theorem azuma_hoeffding_single_step {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (hX : StronglyAdapted ℱ X)
    (n : ℕ) (hn : n = 1) (a b μ : ℕ → ℝ)
    (hab : ∀ t ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, a t ≤ X t ω ∧ X t ω ≤ b t) :
    ((∀ t ∈ Finset.Icc 1 n, P[X t | ℱ (t - 1)] ≤ᵐ[P] fun _ => μ t) →
      ∀ lam : ℝ, 0 < lam →
        P {ω | ∑ t ∈ Finset.Icc 1 n, μ t + lam ≤ ∑ t ∈ Finset.Icc 1 n, X t ω} ≤
          ENNReal.ofReal (Real.exp (-2 * lam ^ 2 / ∑ t ∈ Finset.Icc 1 n, (b t - a t) ^ 2))) ∧
    ((∀ t ∈ Finset.Icc 1 n, (fun _ => μ t) ≤ᵐ[P] P[X t | ℱ (t - 1)]) →
      ∀ lam : ℝ, 0 < lam →
        P {ω | ∑ t ∈ Finset.Icc 1 n, X t ω ≤ ∑ t ∈ Finset.Icc 1 n, μ t - lam} ≤
          ENNReal.ofReal (Real.exp (-2 * lam ^ 2 / ∑ t ∈ Finset.Icc 1 n, (b t - a t) ^ 2))) := by
  sorry

end LefebvreVariations
