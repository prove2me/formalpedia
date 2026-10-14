-- Prove2me | Theorems.Thm_LocalDistanceNetwork_gls_covariance
-- name    : LocalDistanceNetwork.gls_covariance
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T20:25:10.011641+00:00
-- url     : https://prove2.me/theorems/144fcb5d-4010-44c2-8153-4b8b033c3f3a
-- title:
--   Covariance of the $\chi^2$ estimator is $(A^{\mathsf T}C^{-1}A)^{-1}$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have full column rank and let the data covariance matrix $C\in\mathbb R^{m\times m}$ be symmetric positive definite. Let $L=(A^{\mathsf T}C^{-1}A)^{-1}A^{\mathsf T}C^{-1}$ be the estimator matrix of the $\chi^2$ minimization (weight $W=C^{-1}$). Then the covariance matrix of the estimate $LY$ is
--   $$
--   L\,C\,L^{\mathsf T}=(A^{\mathsf T}C^{-1}A)^{-1}.
--   $$
--
--   This is the parameter covariance matrix that the solution procedure reports, from which the uncertainty on $\log_{10}H_0$ is read off.
-- source:
--   H0DN Collaboration (S. Casertano et al.), The Local Distance Network: A community consensus report on the measurement of the Hubble constant at ~1% precision, A&A 708, A166 (2026), https://doi.org/10.1051/0004-6361/202557993, Appendix B (p. 34) and Appendix B.2 (pp. 34-35), Eqs. (B.1)-(B.2)

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS

open Matrix

namespace LocalDistanceNetwork
theorem gls_covariance {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (hA : Function.Injective A.mulVec)
    (C : Matrix m m ℝ) (hC : C.PosDef) :
    linearEstimatorCov (glsEstimatorMatrix A C⁻¹) C = (Aᵀ * C⁻¹ * A)⁻¹ := by sorry
end LocalDistanceNetwork
