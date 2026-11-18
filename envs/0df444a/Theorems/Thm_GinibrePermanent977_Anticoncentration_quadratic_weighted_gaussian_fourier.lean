-- Prove2me | Theorems.Thm_GinibrePermanent977_Anticoncentration_quadratic_weighted_gaussian_fourier
-- name    : GinibrePermanent977.Anticoncentration.quadratic_weighted_gaussian_fourier
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T23:22:38.294479+00:00
-- url     : https://prove2.me/theorems/f58ae606-0219-48c6-ac43-520c9f57c25f
-- title:
--   Quadratic-weighted Gaussian Fourier transform
-- statement:
--   Let $Q$ be a real symmetric positive semidefinite $d\times d$ matrix, let $h\in\mathbb R^d$, and let $Z$ be a standard Gaussian vector. Choose an orthonormal eigenbasis $b_1,\ldots,b_d$ of $Q$, with eigenvalues $\lambda_1,\ldots,\lambda_d$. Then
--
--   $$
--   \mathbb E\exp\bigl(-Z^\top QZ/2+i\langle h,Z\rangle\bigr)
--   =\left(\prod_{j=1}^d(1+\lambda_j)^{-1/2}\right)
--   \exp\left(-\sum_{j=1}^d\frac{\langle h,b_j\rangle^2}{2(1+\lambda_j)}\right).
--   $$
--
--   This is the centered Gaussian formula used for the one-sided bilinear characteristic functions in Lemma 3.1. The spectral product equals $\det(I+Q)^{-1/2}$, and the sum in the exponent equals $h^\top(I+Q)^{-1}h/2$. Singular $Q$ is allowed, because all eigenvalues of $I+Q$ are positive.
--
--   **Formalization Note** The Gaussian law is Mathlib’s standard Gaussian on Euclidean space. The expression uses Mathlib’s chosen orthonormal eigenbasis, giving the spectral-coordinate form of the displayed formula on p.7.
-- source:
--   Koehler and Leung, Anticoncentration of the Permanent in Ginibre Ensembles, STOC 2027 submission #977, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/977.pdf, p.7, proof of Lemma 3.1, displayed centered Gaussian formula.

import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false

theorem GinibrePermanent977.Anticoncentration.quadratic_weighted_gaussian_fourier {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosSemidef) (h : EuclideanSpace ℝ (Fin d)) :
    (∫ y : EuclideanSpace ℝ (Fin d),
      (Real.exp (-inner ℝ y (A.toEuclideanLin y)/2) : ℂ) *
        Complex.exp (Complex.I * (inner ℝ h y : ℝ)) ∂stdGaussian _) =
      (∏ i, ((Real.sqrt (1+hA.1.eigenvalues i))⁻¹ : ℂ)) *
        Complex.exp (-(∑ i, (inner ℝ h (hA.1.eigenvectorBasis i))^2 /
          (2*(1+hA.1.eigenvalues i)) : ℝ)) := by sorry
