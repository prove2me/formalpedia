-- Prove2me | Theorems.Thm_LocalDistanceNetwork_aitken_loewner
-- name    : LocalDistanceNetwork.aitken_loewner
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T20:26:19.403899+00:00
-- url     : https://prove2.me/theorems/2b59a94f-44b8-4d25-8ae4-495ebefdd5eb
-- title:
--   Aitken's theorem, matrix form: $LCL^{\mathsf T}\succeq(A^{\mathsf T}C^{-1}A)^{-1}$ whenever $LA=I$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have full column rank, let $C\in\mathbb R^{m\times m}$ be symmetric positive definite, and let $L\in\mathbb R^{n\times m}$ satisfy $LA=I_n$ (that is, $LY$ is a linear unbiased estimator of $X$ in the model $Y=AX+\varepsilon$, $\mathbb E\varepsilon=0$). Then
--   $$
--   L\,C\,L^{\mathsf T}-(A^{\mathsf T}C^{-1}A)^{-1}\ \text{ is positive semidefinite.}
--   $$
--
--   Since $(A^{\mathsf T}C^{-1}A)^{-1}$ is the covariance of the $\chi^2$ estimator, this is the matrix (Loewner-order) form of the Gauss–Markov–Aitken theorem: no linear unbiased estimator has a smaller covariance.
-- source:
--   H0DN Collaboration (S. Casertano et al.), The Local Distance Network: A community consensus report on the measurement of the Hubble constant at ~1% precision, A&A 708, A166 (2026), https://doi.org/10.1051/0004-6361/202557993, Appendix B (p. 34) and Appendix B.2 (pp. 34-35), Eqs. (B.1)-(B.2)

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS

open Matrix

namespace LocalDistanceNetwork
theorem aitken_loewner {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (hA : Function.Injective A.mulVec)
    (C : Matrix m m ℝ) (hC : C.PosDef)
    (L : Matrix n m ℝ) (hL : L * A = 1) :
    (linearEstimatorCov L C - (Aᵀ * C⁻¹ * A)⁻¹).PosSemidef := by sorry
end LocalDistanceNetwork
