-- Prove2me | Theorems.Thm_GaussianMatrix_gaussian_logsobolev_one_dim_compact_support
-- name    : GaussianMatrix.gaussian_logsobolev_one_dim_compact_support
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T08:06:48.534742+00:00
-- url     : https://prove2.me/theorems/18228d36-19b9-4a84-b45e-ad1977f19088
-- title:
--   Gaussian log-Sobolev inequality for compactly supported $C^1$ functions: $\mathrm{Ent}_\gamma(g^2)\le 2\int (g')^2\,d\gamma$
-- statement:
--   Let $\gamma = N(0,1)$ be the standard Gaussian measure on $\mathbb{R}$, and let $g:\mathbb{R}\to\mathbb{R}$ be continuously differentiable with compact support. Then
--   $$\int g^2\log g^2\,d\gamma-\Big(\int g^2\,d\gamma\Big)\log\Big(\int g^2\,d\gamma\Big)\;\le\;2\int (g')^2\,d\gamma ,$$
--   with the convention $0\log 0=0$.
--
--   This is Gross's inequality restricted to compactly supported test functions. All integrals are finite, so no integrability hypotheses are needed. The general one-dimensional inequality `gaussian_logsobolev_one_dim` follows from this case by multiplying $g$ with smooth cutoffs $\chi(x/n)$ and applying dominated convergence. In turn, this case follows from `gaussian_logsobolev_bounded_below` applied to $g^2+\varepsilon$, letting $\varepsilon\downarrow 0$.
--
--   **Formalization Note.** The derivative is `deriv g` and $C^1$ is `ContDiff ℝ 1 g`. `Real.log 0 = 0` matches $0\log 0 = 0$, and $g\equiv 0$ gives $0\le 0$.
-- source:
--   L. Gross, Logarithmic Sobolev inequalities, Amer. J. Math. 97 (1975), 1061–1083 (Gaussian case); M. Ledoux, The Concentration of Measure Phenomenon (AMS, 2001), Theorem 5.1 / inequality (5.3); D. Bakry, I. Gentil, M. Ledoux, Analysis and Geometry of Markov Diffusion Operators (Springer, 2014), Proposition 5.5.1. Theorem and equation numbers are cited from memory and should be checked.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem gaussian_logsobolev_one_dim_compact_support (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) :
    ∫ t, g t ^ 2 * Real.log (g t ^ 2) ∂(gaussianReal 0 1)
      - (∫ t, g t ^ 2 ∂(gaussianReal 0 1)) * Real.log (∫ t, g t ^ 2 ∂(gaussianReal 0 1))
      ≤ 2 * ∫ t, deriv g t ^ 2 ∂(gaussianReal 0 1) := by
  sorry

end GaussianMatrix
