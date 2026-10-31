-- Prove2me | Theorems.Thm_FoundationsRL_LSVI_lemma_26
-- name    : FoundationsRL.LSVI.lemma_26
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:22:39.827153+00:00
-- url     : https://prove2.me/theorems/9f8d2d29-c26e-4bf8-93d7-2cc6c4fe643c
-- title:
--   Lemma 26, pp. 134–135 — least squares with outcomes indexed by a finite latent set
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $G$ be a finite set, $x_1,\dots,x_T\in\mathcal X$ fixed, and $\mathcal F$ a finite class of functions $\mathcal X\to\mathbb R$. For each $g\in G$ let $y_1(g),\dots,y_T(g)$ be real outcomes with
--   $$
--   \mathbb E[y_i(g)]=f_g(x_i)\quad\text{for some } f_g\in\mathcal F,
--   $$
--   such that each $y_i(g)-f_g(x_i)$ is sub-Gaussian with variance proxy $1$ and $y_1(g),\dots,y_T(g)$ are independent (for different $g$ the outcomes may be correlated). For each $g$ let $\hat f_g\in\arg\min_{f\in\mathcal F}\sum_{i=1}^T(y_i(g)-f(x_i))^2$. Then for every $\delta>0$, with probability at least $1-\delta$, simultaneously for all $g\in G$,
--   $$
--   \sum_{i=1}^T\big(\hat f_g(x_i)-f_g(x_i)\big)^2\le C\log\frac{|\mathcal F||G|}{\delta}.
--   $$
--
--   The latent index $g$ models a regression target that is chosen from a finite family; the price of uniformity over the family is only $\log|G|$. LSVI-UCB faces this situation with $g$ the next-layer value estimate, but with adaptively collected data.
--
--   Differences from the source:
--   - reading: F ⊆ {f : X → ℝ} with |F| in the bound → F a finite set of functions (Finset); reason: the bound contains log |F| and is empty for infinite F; the proof's union bound runs over F
--   - encoding: E[y_i(g) | x_i] = f_g(x_i) with y_i(g) 1-sub-Gaussian, x₁, …, x_T fixed → y_i(g) − f_g(x_i) has a sub-Gaussian moment generating function with variance proxy 1 (HasSubgaussianMGF); reason: Definition 2 (p. 10) with σ² = 1; with x fixed the conditional mean is the mean, and the moment generating function bound forces mean 0
--   - encoding: y₁(g), …, y_T(g) conditionally independent given x₁, …, x_T → independent (iIndepFun) for each g; reason: x is fixed; the families for different g may be correlated, as the footnote allows
--   - encoding: f̂_g ∈ arg min_{f∈F} Σ_i (y_i(g) − f(x_i))² → any selection f̂_g(ω) ∈ F minimizing the empirical loss at every ω; reason: every tie-breaking rule is covered
--   - encoding: ≲ log(|F||G|/δ) → ≤ C log(|F||G|/δ) with one absolute C quantified before all types and data; reason: the meaning of ≲
--   - encoding: "with probability at least 1 − δ" → the outer measure of the bad event is at most δ; reason: equivalent when the event is measurable; no measurability of the selections is needed
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 26, pp. 134–135, with Definition 2, p. 10

import Mathlib

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.LSVI

universe u v w

/-- **Lemma 26** (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision
Making*, arXiv:2312.16730v1, Lemma 26, pp. 134–135): least squares with outcomes indexed by a
finite latent set. There is an absolute constant `C` such that the following holds. Let `G` be a
finite set, `x₁, …, x_T ∈ X` fixed, and `F` a finite class of functions `X → ℝ`. For each
`g ∈ G` let `y₁(g), …, y_T(g)` be outcomes with `E[y_i(g)] = f_g(x_i)` for some `f_g ∈ F`, such
that `y_i(g) − f_g(x_i)` is `1`-sub-Gaussian and `y₁(g), …, y_T(g)` are independent (the
families for different `g` may be correlated). Let `f̂_g ∈ arg min_{f ∈ F} Σ_i (y_i(g) − f(x_i))²`
(any selection). Then for every `δ > 0`, with probability at least `1 − δ`, simultaneously for all
`g ∈ G`, `Σ_{i=1}^T (f̂_g(x_i) − f_g(x_i))² ≤ C log(|F||G|/δ)`.

**Formalization Note.** With `x` fixed, "`E[y_i(g) | x_i] = f_g(x_i)`, `1`-sub-Gaussian" is
`HasSubgaussianMGF (y_i(g) − f_g(x_i)) 1` (Definition 2, p. 10; a centred variable with this
moment generating function bound has mean `0`), and conditional independence given `x` is
independence. The probability of the bad event is bounded through the outer measure, so no
measurability of the selection `f̂` is required. -/
theorem lemma_26 :
    ∃ C : ℝ, ∀ {Ω : Type u} {X : Type v} {G : Type w} [MeasurableSpace Ω] [Fintype G]
      (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ) (x : Fin T → X) (F : Finset (X → ℝ))
      (f : G → X → ℝ) (y : G → Fin T → Ω → ℝ) (fhat : G → Ω → X → ℝ) (δ : ℝ),
      (∀ g, f g ∈ F) →
      (∀ g i, HasSubgaussianMGF (fun ω => y g i ω - f g (x i)) 1 P) →
      (∀ g, iIndepFun (fun i => y g i) P) →
      (∀ g ω, fhat g ω ∈ F) →
      (∀ g ω, ∀ f' ∈ F,
        ∑ i, (y g i ω - fhat g ω (x i)) ^ 2 ≤ ∑ i, (y g i ω - f' (x i)) ^ 2) →
      0 < δ →
      P {ω | ∃ g, C * Real.log ((F.card : ℝ) * Fintype.card G / δ) <
          ∑ i, (fhat g ω (x i) - f g (x i)) ^ 2} ≤ ENNReal.ofReal δ := by sorry

end FoundationsRL.LSVI
