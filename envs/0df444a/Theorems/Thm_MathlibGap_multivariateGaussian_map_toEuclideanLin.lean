-- Prove2me | Theorems.Thm_MathlibGap_multivariateGaussian_map_toEuclideanLin
-- name    : MathlibGap.multivariateGaussian_map_toEuclideanLin
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T22:12:35.50173+00:00
-- url     : https://prove2.me/theorems/d68a4d88-fffb-55da-84c6-aa11a93e2f89
-- title:
--   A linear image of a centred multivariate Gaussian is Gaussian with covariance $A\Sigma A^{\mathsf T}$
-- statement:
--   Let $\Sigma$ be a positive semidefinite $n\times n$ matrix and $A$ an $m\times n$ matrix. If $X\sim N(0,\Sigma)$ on $\mathbb R^n$, then
--   $$AX\sim N\big(0,\ A\Sigma A^{\mathsf T}\big)$$
--   on $\mathbb R^m$.
--
--   **Formalization Note** The law is Mathlib's `multivariateGaussian 0 S` on `EuclideanSpace ℝ (Fin n)`, and $x\mapsto Ax$ is `(Matrix.toEuclideanLin A).toContinuousLinearMap`. Mathlib at this revision has no lemma for the image of `multivariateGaussian` under a linear map.
-- source:
--   Wikipedia, Multivariate normal distribution, https://en.wikipedia.org/wiki/Multivariate_normal_distribution (accessed 2026-11-26), section 'Properties' > 'Affine transformation' (Y = c + BX ~ N(c + Bμ, BΣBᵀ)), the case c = 0, μ = 0

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace MathlibGap

theorem multivariateGaussian_map_toEuclideanLin {m n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosSemidef) (A : Matrix (Fin m) (Fin n) ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S).map
        (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)) =
      multivariateGaussian 0 (A * S * Aᵀ) := by sorry

end MathlibGap
