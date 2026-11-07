-- Prove2me | Theorems.Thm_GaussTesting_lemma_2_14
-- name    : GaussTesting.lemma_2_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:58:57.303036+00:00
-- url     : https://prove2.me/theorems/2aef9e7a-c608-4b3a-b0bb-cec240752ce4
-- title:
--   Lemma 2.14 — distinguishing Bernoulli distributions with $O(\log(1/\delta)/(\sqrt{p_2}-\sqrt{p_1})^2)$ samples
-- statement:
--   Let $0\le p_1<p_2\le1$ and $0<\delta<1$, and consider two Bernoulli distributions with means $p_1$ and $p_2$. Let $\theta=\theta(p_1,p_2)$ be the threshold
--
--   $$
--   \theta=\frac{\log\frac{1-p_1}{1-p_2}}{\log\frac{p_2(1-p_1)}{p_1(1-p_2)}}\ \text{ if } p_1\ne0,\ p_2\ne1,\qquad \theta=\frac{p_2+p_1}{2}\ \text{ otherwise}.
--   $$
--
--   Take the mean $\hat p$ of $k$ independent samples and return $1$ if $\hat p\le\theta$ and $2$ if $\hat p>\theta$. There is an absolute constant $A>0$ such that whenever
--
--   $$
--   k\ \ge\ A\,\frac{\log(1/\delta)}{(\sqrt{p_2}-\sqrt{p_1})^2},
--   $$
--
--   this rule succeeds with probability at least $1-\delta$ under each mean:
--
--   $$
--   \Pr_{p_1}[\hat p>\theta]\le\delta\qquad\text{and}\qquad\Pr_{p_2}[\hat p\le\theta]\le\delta ,
--   $$
--
--   where $k\hat p$ is $\mathrm{Binomial}(k,p)$.
--
--   This is the statistical step that turns the two-sided bound on a base tester's rejection probability into the copy count of Algorithm 1.
--
--   Differences from the source:
--   - reading: Let k = O(log(1/δ)/(√p₂ − √p₁)²) → ∃ absolute A > 0 such that the conclusion holds for every k ≥ A · log(1/δ)/(√p₂ − √p₁)²; reason: the standard meaning of a sufficient sample size; the error bounds are monotone in k
--   - encoding: the probability of misclassification under each mean → binomial sums Σ_{j : θ < j/k} C(k, j) p₁^j (1 − p₁)^{k−j} and Σ_{j : j/k ≤ θ} C(k, j) p₂^j (1 − p₂)^{k−j}; reason: kp̂ is binomial; same quantity
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Lemma 2.14, p.19

import Definitions.Def_GaussTesting_threshold

namespace GaussTesting

/-- **Lemma 2.14 (Distinguishing Bernoulli distributions).** There is an absolute constant `A > 0`
such that for all `0 ≤ p₁ < p₂ ≤ 1`, `0 < δ < 1` and every number of samples
`k ≥ A · log(1/δ)/(√p₂ − √p₁)²`, the rule "return 1 if the sample mean `p̂ ≤ θ`, 2 if `p̂ > θ`" with
the threshold `θ = threshold p₁ p₂` errs with probability at most `δ` under each mean:
`Pr_{p₁}[p̂ > θ] ≤ δ` and `Pr_{p₂}[p̂ ≤ θ] ≤ δ`, where `k p̂ ~ Binomial(k, p)`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), Lemma 2.14, p.19.

**Formalization Note.** "Let `k = O(log(1/δ)/(√p₂−√p₁)²)`" is pinned as "every `k ≥ A·log(1/δ)/(√p₂−√p₁)²`"
with `A` absolute. The error probabilities are written as binomial sums over `j = k p̂ ∈ {0, …, k}`; the
bound forces `k ≥ 1`, so `p̂ = j/k` has no division by zero. -/
theorem lemma_2_14 :
    ∃ A : ℝ, 0 < A ∧ ∀ (p₁ p₂ δ : ℝ) (k : ℕ), 0 ≤ p₁ → p₁ < p₂ → p₂ ≤ 1 → 0 < δ → δ < 1 →
      A * Real.log (1 / δ) / (Real.sqrt p₂ - Real.sqrt p₁) ^ 2 ≤ k →
      (∑ j ∈ (Finset.range (k + 1)).filter (fun j : ℕ => threshold p₁ p₂ < (j : ℝ) / k),
          (k.choose j : ℝ) * p₁ ^ j * (1 - p₁) ^ (k - j)) ≤ δ ∧
      (∑ j ∈ (Finset.range (k + 1)).filter (fun j : ℕ => (j : ℝ) / k ≤ threshold p₁ p₂),
          (k.choose j : ℝ) * p₂ ^ j * (1 - p₂) ^ (k - j)) ≤ δ := by sorry

end GaussTesting
