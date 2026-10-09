-- Prove2me | Theorems.Thm_GaussianMatrix_lipschitz_smooth_approx
-- name    : GaussianMatrix.lipschitz_smooth_approx
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T07:50:28.834868+00:00
-- url     : https://prove2.me/theorems/3d686a2d-134d-40ed-bad2-1c16df9d494a
-- title:
--   Smooth uniform approximation of Euclidean-Lipschitz functions on $\mathbb{R}^\iota$ preserving the Lipschitz constant
-- statement:
--   Let $\iota$ be a finite index set, $L\in\mathbb{R}$, and let $f : \mathbb{R}^\iota \to \mathbb{R}$ satisfy
--   $$|f(x)-f(y)| \le L\Big(\sum_{i\in\iota}(x_i-y_i)^2\Big)^{1/2}\qquad\text{for all } x,y .$$
--   Then for every $\varepsilon > 0$ there is a $C^\infty$ function $g : \mathbb{R}^\iota\to\mathbb{R}$ satisfying the same Lipschitz bound,
--   $$|g(x)-g(y)| \le L\Big(\sum_{i\in\iota}(x_i-y_i)^2\Big)^{1/2},$$
--   and $|g(x) - f(x)| \le \varepsilon$ for every $x$.
--
--   One may take $g = \psi * f$, the convolution of $f$ with a smooth probability density $\psi$ supported in a small ball. This lemma lets one prove functional inequalities for Lipschitz functions from their versions for smooth functions with bounded gradient, without Rademacher's theorem; here it transfers the Gaussian log-Sobolev inequality to the entropy bound for $e^{sf}$ with $f$ Lipschitz.
--
--   **Formalization Note.** Smoothness is expressed as `∀ n : ℕ, ContDiff ℝ n g`. No sign condition on $L$ is imposed: for nonempty $\iota$ the hypothesis forces $L \ge 0$, and for $\iota=\emptyset$ everything is constant.
-- source:
--   Standard fact (mollification): if $f$ is $L$-Lipschitz for the Euclidean distance and $\psi \ge 0$ is a $C^\infty$ function with $\int\psi = 1$ supported in a ball of radius $r$, then $\psi * f$ is $C^\infty$, $L$-Lipschitz, and $\|\psi * f - f\|_\infty \le L r$ (up to the comparison between the ball's norm and the Euclidean norm); see e.g. L. C. Evans, R. F. Gariepy, Measure Theory and Fine Properties of Functions (CRC Press, 1992), §4.2.1 (mollifiers), cited from memory.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem lipschitz_smooth_approx {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (L : ℝ)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : (ι → ℝ) → ℝ, (∀ n : ℕ, ContDiff ℝ n g) ∧
      (∀ x y, |g x - g y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) ∧
      ∀ x, |g x - f x| ≤ ε := by
  sorry

end GaussianMatrix
