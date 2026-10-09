-- Prove2me | Theorems.Thm_GaussianMatrix_gaussian_ibp_one_dim
-- name    : GaussianMatrix.gaussian_ibp_one_dim
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T08:09:46.482261+00:00
-- url     : https://prove2.me/theorems/71437f64-2896-46cc-9cd6-93a6cc35ef76
-- title:
--   One-dimensional Gaussian integration by parts (Stein's identity): $\int x\,h(x)\,d\gamma=\int h'\,d\gamma$
-- statement:
--   Let $\gamma=N(0,1)$ be the standard Gaussian measure on $\mathbb{R}$, and let $h:\mathbb{R}\to\mathbb{R}$ be differentiable with $|h'(x)|\le C$ for all $x$. Then
--   $$\int x\,h(x)\,d\gamma(x)\;=\;\int h'(x)\,d\gamma(x).$$
--   Equivalently, $\mathbb{E}[Xh(X)]=\mathbb{E}[h'(X)]$ for $X\sim N(0,1)$.
--
--   This is Stein's identity. It follows from integration by parts on the line, since the Gaussian density $\varphi$ satisfies $\varphi'=-x\varphi$. In the semigroup proof of the log-Sobolev inequality it is used twice:
--   - in the noise variable, to compute the second derivative of $P_tf$ for $f\in C^1$;
--   - in the space variable, to identify the entropy derivative with minus the Fisher information.
--
--   **Formalization Note.** The bounded derivative gives $|h(x)|\le|h(0)|+C|x|$, so all integrals are finite. `deriv h` is measurable for any $h$.
-- source:
--   C. Stein, Estimation of the mean of a multivariate normal distribution, Ann. Statist. 9 (1981), 1135–1151, Lemma 1 (one-dimensional case; cited from memory). Standard fact: for $X\sim N(0,1)$ and absolutely continuous $h$ with $\mathbb{E}|h'(X)|<\infty$, $\mathbb{E}[Xh(X)]=\mathbb{E}[h'(X)]$.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem gaussian_ibp_one_dim (h : ℝ → ℝ) (hh : Differentiable ℝ h) (C : ℝ)
    (hdh : ∀ x, |deriv h x| ≤ C) :
    ∫ x, x * h x ∂(gaussianReal 0 1) = ∫ x, deriv h x ∂(gaussianReal 0 1) := by
  sorry

end GaussianMatrix
