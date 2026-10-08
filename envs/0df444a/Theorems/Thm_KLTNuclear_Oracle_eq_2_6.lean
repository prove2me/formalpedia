-- Prove2me | Theorems.Thm_KLTNuclear_Oracle_eq_2_6
-- name    : KLTNuclear.Oracle.eq_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:36.482975+00:00
-- url     : https://prove2.me/theorems/691d7bfb-4aa8-4ed5-ae9e-7299f227d8a4
-- title:
--   (2.6) — first-order necessary condition for $\hat A^\lambda$ over a convex set
-- statement:
--   Let $\mathbb A$ be a **convex** set of $m_1\times m_2$ matrices, $\lambda>0$, and fix a realization of a sample with square-integrable design entries at which $\hat A^\lambda$ minimizes the penalized empirical risk
--   $$L_n(A)=\|A\|^2_{L_2(\Pi)}-\Big\langle\frac2n\sum_{i=1}^nY_iX_i,A\Big\rangle+\lambda\|A\|_1$$
--   over $\mathbb A$. Then there is a subgradient $\hat V\in\partial\|\hat A^\lambda\|_1$ of the nuclear norm at $\hat A^\lambda$ such that, for all $A\in\mathbb A$,
--   $$2\langle\hat A^\lambda,\hat A^\lambda-A\rangle_{L_2(\Pi)}-\Big\langle\frac2n\sum_{i=1}^nY_iX_i,\hat A^\lambda-A\Big\rangle+\lambda\langle\hat V,\hat A^\lambda-A\rangle\le0 .$$
--
--   This is the variational inequality expressing that $0$ lies in the subdifferential of $L_n$ plus the normal cone of $\mathbb A$ at $\hat A^\lambda$; it is the entry point of the "fast rate" part of Theorem 1.
--
--   **Formalization Note** $\hat V\in\partial\|\hat A^\lambda\|_1$ means $\|\hat A^\lambda\|_1+\langle\hat V,B-\hat A^\lambda\rangle\le\|B\|_1$ for every $B$. The model (1.1) is not needed for this step and is not assumed; the sample regularity conditions are.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 7, (2.6)

import Mathlib
import Definitions.Def_KLTNuclear_Oracle_Model

open MeasureTheory MatrixCompletion

namespace KLTNuclear.Oracle

/-- (2.6) (p. 7): first-order necessary condition for the estimator over a convex set 𝔸. -/
theorem eq_2_6 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → RealMatrix m₁ m₂) (Y : Fin n → Ω → ℝ)
    (hreg : SampleRegularity P X Y)
    (𝔸 : Set (RealMatrix m₁ m₂)) (h𝔸 : Convex ℝ 𝔸) (lam : ℝ) (hlam : 0 < lam)
    (ω : Ω) (Ahat : RealMatrix m₁ m₂) (hAhat : IsEstimator P X Y lam ω 𝔸 Ahat) :
    ∃ Vhat : RealMatrix m₁ m₂, IsNuclearSubgradient Ahat Vhat ∧
      ∀ A ∈ 𝔸, 2 * l2Inner P X Ahat (Ahat - A) - matrixInner (empiricalYX X Y ω) (Ahat - A) +
        lam * matrixInner Vhat (Ahat - A) ≤ 0 := by sorry

end KLTNuclear.Oracle
