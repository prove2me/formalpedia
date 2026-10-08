-- Prove2me | Theorems.Thm_FriendlyShadow_Gaussian_lemma_45
-- name    : FriendlyShadow.Gaussian.lemma_45
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:18:19.011987+00:00
-- url     : https://prove2.me/theorems/e9d16d44-7a0b-4d9c-b2d6-c078a45c68e6
-- title:
--   Lemma 45, p. 34 — LG_d(ā, σ, 4√(d log n)) is 4σ⁻¹√(d log n)-log-Lipschitz, R_{n,d} ≤ 4σ√(d log n), rₙ ≤ 4σ√(log n), τ ≥ σ/4
-- statement:
--   Let $n\ge d\ge3$, $\sigma>0$, $\bar a\in\mathbb R^d$, and let $\mu$ be the density of the $(\sigma,4\sqrt{d\log n})$-Laplace–Gaussian distribution with mean $\bar a$. Then $\mu$ is a probability density with mean $\bar a$, and:
--   1. $\mu$ is $4\sigma^{-1}\sqrt{d\log n}$-log-Lipschitz;
--   2. its cutoff radius satisfies $R_{n,d}\le4\sigma\sqrt{d\log n}$;
--   3. its $n$-th deviation satisfies $r_n\le4\sigma\sqrt{\log n}$;
--   4. its line variance is at least $\tau^2$ with $\tau=\sigma/4$.
--
--   Plugged into Theorem 22, these give
--   $$\frac L\tau\le\frac{16\sqrt{d\log n}}{\sigma^2},\qquad 1+R_{n,d}\le1+4\sigma\sqrt{d\log n},\qquad 1+4r_n\le1+16\sigma\sqrt{\log n},$$
--   the factors of the goal bound.
--
--   **Formalization Note** The two extra conjuncts (probability density, mean $\bar a$) are what "the distribution with mean $\bar a$" asserts on the page, and Theorem 22 needs them. The parameter claims use the upper-bound (lower bound for $\tau$) predicates of the definitions file.
-- source:
--   Dadush & Huiberts, arXiv:1711.05667v4, Lemma 45, p. 34

import Mathlib
import Definitions.Def_FriendlyShadow_Gaussian_Model

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace FriendlyShadow.Gaussian

/-- Lemma 45 (p. 34). For `n ≥ d ≥ 3` and `σ > 0`, the normalised density `μ` of the
`(σ, 4√(d log n))`-Laplace–Gaussian distribution on `ℝᵈ` with mean `ā` is a probability density
with mean `ā`, is `4σ⁻¹√(d log n)`-log-Lipschitz, has cutoff radius `R_{n,d} ≤ 4σ√(d log n)`,
`n`-th deviation `rₙ ≤ 4σ√(log n)`, and line variance at least `(σ/4)²`. -/
theorem lemma_45 {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n) (σ : ℝ) (hσ : 0 < σ)
    (abar : EuclideanSpace ℝ (Fin d)) (μ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hμ : μ = lgPdf abar σ (4 * Real.sqrt (d * Real.log n))) :
    IsDensity μ ∧ HasMean μ abar ∧
      LogLipschitz μ (4 * σ⁻¹ * Real.sqrt (d * Real.log n)) ∧
      CutoffRadiusLE μ abar (cutoffLevel n d) (4 * σ * Real.sqrt (d * Real.log n)) ∧
      NthDeviationLE μ abar n (4 * σ * Real.sqrt (Real.log n)) ∧
      LineVarianceGE μ (σ / 4) := by sorry

end FriendlyShadow.Gaussian
