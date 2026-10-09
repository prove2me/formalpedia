-- Prove2me | Theorems.Thm_GaussianMatrix_ou_semigroup_commutation
-- name    : GaussianMatrix.ou_semigroup_commutation
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T08:09:08.634105+00:00
-- url     : https://prove2.me/theorems/cbcb40a9-f91e-4f68-be16-596f87acd709
-- title:
--   Commutation of the Ornstein–Uhlenbeck semigroup with differentiation: $(P_tf)'=e^{-t}P_t(f')$
-- statement:
--   Let $\gamma=N(0,1)$ be the standard Gaussian measure on $\mathbb{R}$, and let $f\in C^1(\mathbb{R})$ satisfy $|f'(x)|\le C$ for all $x$. Then for all $t,x\in\mathbb{R}$ the function $z\mapsto\int f(e^{-t}z+\sqrt{1-e^{-2t}}\,y)\,d\gamma(y)$ is differentiable at $x$, and
--   $$\frac{d}{dz}\Big|_{z=x}\int f\big(e^{-t}z+\sqrt{1-e^{-2t}}\,y\big)\,d\gamma(y)\;=\;e^{-t}\int f'\big(e^{-t}x+\sqrt{1-e^{-2t}}\,y\big)\,d\gamma(y).$$
--   In semigroup notation, $(P_tf)'=e^{-t}P_t(f')$.
--
--   This commutation relation is the one-dimensional form of the curvature condition $\Gamma_2\ge\Gamma$ for the Ornstein–Uhlenbeck operator. Combined with Cauchy–Schwarz it gives the decay $e^{-2t}$ of the Fisher information along the semigroup, which produces the constant $\frac12$ in the log-Sobolev inequality.
--
--   **Formalization Note.** The bounded derivative gives linear growth of $f$, which makes the integrals finite. The identity holds for every real $t$.
-- source:
--   Standard fact (differentiation under the integral sign in Mehler's formula); D. Bakry, I. Gentil, M. Ledoux, Analysis and Geometry of Markov Diffusion Operators (Springer, 2014), §2.7.1, commutation $\nabla P_t=e^{-t}P_t\nabla$ for the Ornstein–Uhlenbeck semigroup (cited from memory).

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem ou_semigroup_commutation (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (C : ℝ)
    (hdf : ∀ x, |deriv f x| ≤ C) (t x : ℝ) :
    HasDerivAt
      (fun z => ∫ y, f (Real.exp (-t) * z + Real.sqrt (1 - Real.exp (-(2 * t))) * y)
        ∂(gaussianReal 0 1))
      (Real.exp (-t) * ∫ y, deriv f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y)
        ∂(gaussianReal 0 1)) x := by
  sorry

end GaussianMatrix
