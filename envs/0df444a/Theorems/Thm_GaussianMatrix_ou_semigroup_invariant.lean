-- Prove2me | Theorems.Thm_GaussianMatrix_ou_semigroup_invariant
-- name    : GaussianMatrix.ou_semigroup_invariant
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T08:08:34.553594+00:00
-- url     : https://prove2.me/theorems/504ceb37-906c-42ce-b475-d350aa6b3102
-- title:
--   Invariance of $N(0,1)$ under the Ornstein–Uhlenbeck semigroup: $\int P_th\,d\gamma=\int h\,d\gamma$
-- statement:
--   Let $\gamma=N(0,1)$ be the standard Gaussian measure on $\mathbb{R}$, let $t\ge0$, and let $h:\mathbb{R}\to\mathbb{R}$ be $\gamma$-integrable. Then
--   $$\int\!\!\int h\big(e^{-t}x+\sqrt{1-e^{-2t}}\,y\big)\,d\gamma(y)\,d\gamma(x)\;=\;\int h\,d\gamma ,$$
--   that is, $\int P_th\,d\gamma=\int h\,d\gamma$ for the Ornstein–Uhlenbeck semigroup $P_t$.
--
--   This expresses the invariance of $\gamma$ under $P_t$. Equivalently, for independent standard Gaussians $X,Y$ and $a^2+b^2=1$, the variable $aX+bY$ is standard Gaussian. It is used to bound the integrated Fisher information of $P_tf$ by $e^{-2t}$ times that of $f$.
--
--   **Formalization Note.** The hypothesis $t\ge0$ is needed: for $t<0$ Lean's `Real.sqrt` of the negative number $1-e^{-2t}$ is $0$, and the statement fails.
-- source:
--   Standard fact: if $X,Y$ are independent $N(0,1)$ random variables and $a^2+b^2=1$ then $aX+bY\sim N(0,1)$; hence $\gamma$ is invariant for the Ornstein–Uhlenbeck semigroup. See D. Bakry, I. Gentil, M. Ledoux, Analysis and Geometry of Markov Diffusion Operators (Springer, 2014), §2.7.1 (cited from memory).

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem ou_semigroup_invariant (h : ℝ → ℝ) (hh : Integrable h (gaussianReal 0 1)) (t : ℝ)
    (ht : 0 ≤ t) :
    ∫ x, (∫ y, h (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y)
        ∂(gaussianReal 0 1)) ∂(gaussianReal 0 1)
      = ∫ x, h x ∂(gaussianReal 0 1) := by
  sorry

end GaussianMatrix
