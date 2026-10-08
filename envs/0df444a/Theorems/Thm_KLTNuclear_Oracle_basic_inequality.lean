-- Prove2me | Theorems.Thm_KLTNuclear_Oracle_basic_inequality
-- name    : KLTNuclear.Oracle.basic_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:25.371091+00:00
-- url     : https://prove2.me/theorems/4df2855f-cd0a-4525-b702-a18058fff8ab
-- title:
--   Proof of Theorem 1 — the basic inequality $\|\hat A^\lambda-A_0\|^2_{L_2(\Pi)}\le\|A-A_0\|^2_{L_2(\Pi)}+2\Delta\|\hat A^\lambda-A\|_1+\lambda(\|A\|_1-\|\hat A^\lambda\|_1)$
-- statement:
--   Work in the trace regression model $\mathbb E(Y_i\mid X_i)=\langle A_0,X_i\rangle$, $i=1,\dots,n$, with square-integrable design entries and integrable responses. Fix a realization of the sample, a set $\mathbb A$ of $m_1\times m_2$ matrices, $\lambda>0$, and an estimator $\hat A^\lambda\in\operatorname{argmin}_{A\in\mathbb A}L_n(A)$ for the penalized empirical risk
--   $$L_n(A)=\|A\|^2_{L_2(\Pi)}-\Big\langle\frac2n\sum_{i=1}^nY_iX_i,A\Big\rangle+\lambda\|A\|_1 .$$
--   Let $\mathbf M=\frac1n\sum_{i=1}^n(Y_iX_i-\mathbb E(Y_iX_i))$ and $\Delta=\|\mathbf M\|_\infty$ (operator norm). Then for every $A\in\mathbb A$,
--   $$\|\hat A^\lambda-A_0\|^2_{L_2(\Pi)}\le\|A-A_0\|^2_{L_2(\Pi)}+2\Delta\|\hat A^\lambda-A\|_1+\lambda\big(\|A\|_1-\|\hat A^\lambda\|_1\big).$$
--
--   No condition relating $\lambda$ and $\Delta$ and no structure of $\mathbb A$ is needed. This inequality is the starting point of the proof of Theorem 1; under $\lambda\ge2\Delta$ it gives (2.3) immediately.
--
--   **Formalization Note** The model hypothesis is the conditional-expectation form of (1.1); the sample regularity (measurability, square-integrable design entries, integrable $Y_i$ and $Y_i(X_i)_{jk}$) is added so that the expectations are meaningful. Independence of the pairs is not assumed (the statement holds realization by realization).
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 7, proof of Theorem 1, display after 'which implies, due to the trace duality'

import Mathlib
import Definitions.Def_KLTNuclear_Oracle_Model

open MeasureTheory MatrixCompletion

namespace KLTNuclear.Oracle

/-- Proof of Theorem 1 (p. 7), display after "which implies, due to the trace duality":
the basic inequality, with Δ = ‖𝐌‖∞. -/
theorem basic_inequality {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → RealMatrix m₁ m₂) (Y : Fin n → Ω → ℝ)
    (hreg : SampleRegularity P X Y)
    (A₀ : RealMatrix m₁ m₂) (hmodel : TraceRegressionModel P X Y A₀)
    (𝔸 : Set (RealMatrix m₁ m₂)) (lam : ℝ) (hlam : 0 < lam)
    (ω : Ω) (Ahat : RealMatrix m₁ m₂) (hAhat : IsEstimator P X Y lam ω 𝔸 Ahat) :
    ∀ A ∈ 𝔸, l2NormSq P X (Ahat - A₀) ≤
      l2NormSq P X (A - A₀) + 2 * spectralNorm (noiseMatrix P X Y ω) * nuclearNorm (Ahat - A) +
        lam * (nuclearNorm A - nuclearNorm Ahat) := by sorry

end KLTNuclear.Oracle
