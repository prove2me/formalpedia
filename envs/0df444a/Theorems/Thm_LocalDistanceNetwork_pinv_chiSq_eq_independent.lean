-- Prove2me | Theorems.Thm_LocalDistanceNetwork_pinv_chiSq_eq_independent
-- name    : LocalDistanceNetwork.pinv_chiSq_eq_independent
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T20:31:10.571355+00:00
-- url     : https://prove2.me/theorems/46c1bf5c-bd6a-43f5-8784-d155824f7984
-- title:
--   Appendix B.2 — the pseudoinverse $\chi^2$ equals the $\chi^2$ of the independent measurements
-- statement:
--   Suppose the $m$ equations of the system are built from $k$ distinct measurements: there is a vector $Z\in\mathbb R^{k}$ of measurements with symmetric positive-definite covariance $S\in\mathbb R^{k\times k}$, and a matrix $B\in\mathbb R^{m\times k}$ of full column rank such that the data vector is $Y=BZ$. The data covariance $C=BSB^{\mathsf T}$ is then singular whenever $m>k$. Suppose moreover that the model is expressed through the measurements, i.e. the coefficient matrix is $A=BA_0$ for some $A_0\in\mathbb R^{k\times n}$. Let $P$ be a Moore–Penrose inverse of $C$. Then:
--
--   1. for every parameter vector $X\in\mathbb R^{n}$,
--   $$
--   (Y-AX)^{\mathsf T}P\,(Y-AX)=(Z-A_0X)^{\mathsf T}S^{-1}(Z-A_0X);
--   $$
--   2. the corresponding GLS estimates coincide:
--   $$
--   (A^{\mathsf T}PA)^{-1}A^{\mathsf T}P\,Y=(A_0^{\mathsf T}S^{-1}A_0)^{-1}A_0^{\mathsf T}S^{-1}Z .
--   $$
--
--   So the $\chi^2$ computed with the pseudoinverse of the (singular) covariance matrix of all $m$ equations is exactly the $\chi^2$ of the $k$ linearly independent measurements, and both lead to the same solution.
--
--   **Formalization Note** The inverses in item 2 are Mathlib matrix inverses (equal to $0$ for singular matrices); item 2 holds as stated without assuming $A_0$ has full column rank.
-- source:
--   H0DN Collaboration (S. Casertano et al.), The Local Distance Network: A community consensus report on the measurement of the Hubble constant at ~1% precision, A&A 708, A166 (2026), https://doi.org/10.1051/0004-6361/202557993, Appendix B (p. 34) and Appendix B.2 (pp. 34-35), Eqs. (B.1)-(B.2)

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS

open Matrix

namespace LocalDistanceNetwork
theorem pinv_chiSq_eq_independent {m k n : Type*} [Fintype m] [Fintype k] [Fintype n]
    [DecidableEq k] [DecidableEq n]
    (S : Matrix k k ℝ) (hS : S.PosDef)
    (B : Matrix m k ℝ) (hB : Function.Injective B.mulVec)
    (A₀ : Matrix k n ℝ) (Z : k → ℝ)
    (P : Matrix m m ℝ) (hP : IsMoorePenroseInverse (B * S * Bᵀ) P) :
    (∀ X : n → ℝ, glsObjective (B * A₀) P (B *ᵥ Z) X = glsObjective A₀ S⁻¹ Z X) ∧
    glsEstimate (B * A₀) P (B *ᵥ Z) = glsEstimate A₀ S⁻¹ Z := by sorry
end LocalDistanceNetwork
