-- Prove2me | Theorems.Thm_FournierGuillin_Conc_lemma_9
-- name    : FournierGuillin.Conc.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:22.124993+00:00
-- url     : https://prove2.me/theorems/cc6e07ff-b67b-4c0b-bc8f-032a299cd133
-- title:
--   Lemma 9, p. 10 — Poisson(λ) mgf, two-sided mgf bound and tail bounds via f and g
-- statement:
--   Let $\lambda>0$ and let $X$ be Poisson($\lambda$)-distributed. Then
--
--   1. $\mathbb E\,e^{\theta X}=\exp(\lambda(e^\theta-1))$ for all $\theta\in\mathbb R$;
--   2. $\mathbb E\,e^{\theta|X-\lambda|}\le2\exp(\lambda(e^\theta-1-\theta))$ for all $\theta>0$;
--   3. $\mathbb P(X>\lambda x)\le\exp(-\lambda g(x))$ for all $x>0$;
--   4. $\mathbb P(|X-\lambda|>\lambda x)\le2\exp(-\lambda f(x))$ for all $x>0$;
--   5. $\mathbb P(X>\lambda x)\le\lambda$ for all $x>0$,
--
--   with $f(x)=(1+x)\log(1+x)-x$ and $g(x)=(x\log x-x+1)\mathbf 1_{\{x\ge1\}}$ (Notation 7).
--
--   These are the Poisson concentration facts used to control the number of points and the cell counts of the Poisson measure in Proposition 8.
--
--   **Formalization Note** The page's $\lambda$ is `r : ℝ≥0` (with `0 < r`) in Lean, since `λ` is a keyword. The law of $X$ is Mathlib's `poissonMeasure r` on $\mathbb N$. Expectations are lower Lebesgue integrals in $[0,\infty]$, so (b) cannot hold by a junk zero value of a non-integrable integral.
-- source:
--   Fournier & Guillin, arXiv:1312.2128v1, Lemma 9, p. 10; Notation 7, p. 9

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_FournierGuillin_Conc_Setting
open MeasureTheory WassersteinDRO.Duality
open scoped ENNReal NNReal

namespace FournierGuillin.Conc

/-- Lemma 9 (p. 10): for `λ > 0` (here `r`) and `X` Poisson(`λ`)-distributed,
(a) `E exp(θX) = exp(λ(e^θ - 1))` for all real `θ`;
(b) `E exp(θ|X - λ|) ≤ 2 exp(λ(e^θ - 1 - θ))` for `θ > 0`;
(c) `ℙ(X > λx) ≤ exp(-λ g(x))` for `x > 0`;
(d) `ℙ(|X - λ| > λx) ≤ 2 exp(-λ f(x))` for `x > 0`;
(e) `ℙ(X > λx) ≤ λ` for `x > 0`.
Expectations are lower Lebesgue integrals against the Poisson law on `ℕ`. -/
theorem lemma_9 (r : ℝ≥0) (hr : 0 < r) :
    (∀ θ : ℝ, ∫⁻ n : ℕ, ENNReal.ofReal (Real.exp (θ * n)) ∂ProbabilityTheory.poissonMeasure r =
        ENNReal.ofReal (Real.exp (r * (Real.exp θ - 1)))) ∧
    (∀ θ : ℝ, 0 < θ →
      ∫⁻ n : ℕ, ENNReal.ofReal (Real.exp (θ * |(n : ℝ) - r|)) ∂ProbabilityTheory.poissonMeasure r ≤
        ENNReal.ofReal (2 * Real.exp (r * (Real.exp θ - 1 - θ)))) ∧
    (∀ x : ℝ, 0 < x →
      ProbabilityTheory.poissonMeasure r {n : ℕ | (r : ℝ) * x < n} ≤
        ENNReal.ofReal (Real.exp (-(r * bennettG x)))) ∧
    (∀ x : ℝ, 0 < x →
      ProbabilityTheory.poissonMeasure r {n : ℕ | (r : ℝ) * x < |(n : ℝ) - r|} ≤
        ENNReal.ofReal (2 * Real.exp (-(r * bennettF x)))) ∧
    (∀ x : ℝ, 0 < x →
      ProbabilityTheory.poissonMeasure r {n : ℕ | (r : ℝ) * x < n} ≤ ENNReal.ofReal r) := by sorry

end FournierGuillin.Conc
