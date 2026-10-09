-- Prove2me | Theorems.Thm_GaussianMatrix_gaussian_concentration_vector
-- name    : GaussianMatrix.gaussian_concentration_vector
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T04:24:28.77983+00:00
-- url     : https://prove2.me/theorems/e92f914b-12d3-4963-8bc4-6778100ff946
-- title:
--   Sharp Gaussian concentration for Lipschitz functions of a standard Gaussian vector: $\mathbb{P}\{f(X)\ge\mathbb{E}f(X)+Lt\}\le e^{-t^2/2}$
-- statement:
--   Let $\iota$ be a finite index set and let $\gamma_\iota = \bigotimes_{i\in\iota} N(0,1)$ be the standard Gaussian measure on $\mathbb{R}^\iota$ (independent standard normal coordinates). Let $L > 0$ and let $f : \mathbb{R}^\iota \to \mathbb{R}$ be $L$-Lipschitz for the Euclidean distance, i.e.
--   $$|f(x) - f(y)| \le L \Big(\sum_{i\in\iota} (x_i - y_i)^2\Big)^{1/2} \qquad \text{for all } x, y \in \mathbb{R}^\iota .$$
--   Then $f$ is $\gamma_\iota$-integrable and, for every $t \ge 0$,
--   $$\gamma_\iota\Big\{x \in \mathbb{R}^\iota : f(x) \ge \int f \, d\gamma_\iota + L t\Big\} \;\le\; e^{-t^2/2}.$$
--
--   This is the Tsirelson–Ibragimov–Sudakov inequality with its sharp, dimension-free constant. It is the vector form of Gaussian concentration; the matrix version (`gaussian_concentration`, for Lipschitz functions of a Gaussian matrix with respect to the Frobenius norm) follows from it by flattening a $p\times m$ array into a vector indexed by $\mathrm{Fin}\,p \times \mathrm{Fin}\,m$.
--
--   **Formalization Note.** The measure is `Measure.pi (fun _ : ι => gaussianReal 0 1)` on `ι → ℝ`, and the Euclidean distance is written out as `Real.sqrt (∑ i, (x i - y i) ^ 2)` (the default norm on `ι → ℝ` is the sup norm, which is not used). The hypothesis $L > 0$ is necessary: for $L = 0$ the function is constant and the event has probability $1$. For $\iota = \emptyset$ the function is constant, the event is empty when $t > 0$ and is the whole space when $t = 0$, in which case both sides equal $1$. The measure is compared in `ENNReal` with `ENNReal.ofReal (Real.exp (-t ^ 2 / 2))`.
-- source:
--   B. Tsirelson, I. Ibragimov, V. Sudakov, Norms of Gaussian sample functions (1976); S. Boucheron, G. Lugosi, P. Massart, Concentration Inequalities (Oxford Univ. Press, 2013), Theorem 5.6, §5.4 (Tsirelson–Ibragimov–Sudakov inequality); M. Ledoux, The Concentration of Measure Phenomenon (AMS, 2001), inequality (2.35). Theorem and equation numbers are cited from memory.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem gaussian_concentration_vector {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (L : ℝ)
    (hL : 0 < L) (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable f (Measure.pi fun _ : ι => gaussianReal 0 1) ∧
    (Measure.pi fun _ : ι => gaussianReal 0 1)
        {x | (∫ y, f y ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) + L * t ≤ f x}
      ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := by sorry

end GaussianMatrix
