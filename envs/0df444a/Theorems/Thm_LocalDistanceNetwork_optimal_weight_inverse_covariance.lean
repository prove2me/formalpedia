-- Prove2me | Theorems.Thm_LocalDistanceNetwork_optimal_weight_inverse_covariance
-- name    : LocalDistanceNetwork.optimal_weight_inverse_covariance
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T20:27:50.361092+00:00
-- url     : https://prove2.me/theorems/2a5a614b-223a-4982-9de5-9abb8dfc30fb
-- title:
--   Eq. (B.2) claim — the weight $W=C^{-1}$ gives the lowest variance
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have full column rank, let the data covariance $C\in\mathbb R^{m\times m}$ be symmetric positive definite, and let $W\in\mathbb R^{m\times m}$ be any symmetric positive-definite weight matrix. Write $L_W=(A^{\mathsf T}WA)^{-1}A^{\mathsf T}W$ for the minimizer of the quadratic form (B.2) with weight $W$. Then
--   $$
--   L_W\,C\,L_W^{\mathsf T}-L_{C^{-1}}\,C\,L_{C^{-1}}^{\mathsf T}\ \text{ is positive semidefinite.}
--   $$
--
--   In words: among all weighted least-squares solutions, the one weighted by the inverse covariance matrix has the smallest covariance (in the Loewner order), which justifies using the $\chi^2$ of Eq. (B.1) rather than any other weighting.
-- source:
--   H0DN Collaboration (S. Casertano et al.), The Local Distance Network: A community consensus report on the measurement of the Hubble constant at ~1% precision, A&A 708, A166 (2026), https://doi.org/10.1051/0004-6361/202557993, Appendix B (p. 34) and Appendix B.2 (pp. 34-35), Eqs. (B.1)-(B.2)

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS

open Matrix

namespace LocalDistanceNetwork
theorem optimal_weight_inverse_covariance {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (hA : Function.Injective A.mulVec)
    (C : Matrix m m ℝ) (hC : C.PosDef)
    (W : Matrix m m ℝ) (hW : W.PosDef) :
    (linearEstimatorCov (glsEstimatorMatrix A W) C
      - linearEstimatorCov (glsEstimatorMatrix A C⁻¹) C).PosSemidef := by sorry
end LocalDistanceNetwork
