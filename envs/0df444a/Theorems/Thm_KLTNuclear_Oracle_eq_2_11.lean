-- Prove2me | Theorems.Thm_KLTNuclear_Oracle_eq_2_11
-- name    : KLTNuclear.Oracle.eq_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:33.089278+00:00
-- url     : https://prove2.me/theorems/e34da3e2-c0f3-49f6-b284-b781e48890a0
-- title:
--   (2.11) — the inequality deduced from (2.8) for every $A\in\mathbb A$ with support $(S_1,S_2)$
-- statement:
--   Work in the trace regression model $\mathbb E(Y_i\mid X_i)=\langle A_0,X_i\rangle$ with square-integrable design entries and integrable responses. Let $\mathbb A$ be a **convex** set of $m_1\times m_2$ matrices, $\lambda>0$, and fix a realization of the sample at which $\hat A^\lambda$ minimizes $L_n$ over $\mathbb A$; let $\mathbf M=\frac1n\sum_i(Y_iX_i-\mathbb E(Y_iX_i))$. Then for every $A\in\mathbb A$ with singular value decomposition $A=\sum_{j=1}^r\sigma_ju_jv_j^\top$ and support $(S_1,S_2)$,
--   $$\|\hat A^\lambda-A_0\|^2_{L_2(\Pi)}+\|\hat A^\lambda-A\|^2_{L_2(\Pi)}+\lambda\|P_{S_1^\perp}\hat A^\lambda P_{S_2^\perp}\|_1\le\|A-A_0\|^2_{L_2(\Pi)}+\lambda\|P_{S_1}(\hat A^\lambda-A)P_{S_2}\|_1+2\langle\mathbf M,\hat A^\lambda-A\rangle .$$
--
--   This is the key deterministic inequality of the fast-rate part of Theorem 1; no relation between $\lambda$ and $\|\mathbf M\|_\infty$ is needed for it.
--
--   **Formalization Note** Model hypothesis in conditional-expectation form; integrability conditions added; independence not assumed. The support is given by SVD data `S : SVD A r`.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 8, (2.11)

import Mathlib
import Definitions.Def_KLTNuclear_Oracle_Model

open MeasureTheory MatrixCompletion

namespace KLTNuclear.Oracle

/-- (2.11) (p. 8): for a convex 𝔸 and every A ∈ 𝔸 with support (S₁, S₂). -/
theorem eq_2_11 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → RealMatrix m₁ m₂) (Y : Fin n → Ω → ℝ)
    (hreg : SampleRegularity P X Y)
    (A₀ : RealMatrix m₁ m₂) (hmodel : TraceRegressionModel P X Y A₀)
    (𝔸 : Set (RealMatrix m₁ m₂)) (h𝔸 : Convex ℝ 𝔸) (lam : ℝ) (hlam : 0 < lam)
    (ω : Ω) (Ahat : RealMatrix m₁ m₂) (hAhat : IsEstimator P X Y lam ω 𝔸 Ahat) :
    ∀ A ∈ 𝔸, ∀ (r : ℕ) (S : SVD A r),
      l2NormSq P X (Ahat - A₀) + l2NormSq P X (Ahat - A) + lam * nuclearNorm (normalProjection S Ahat) ≤
        l2NormSq P X (A - A₀) + lam * nuclearNorm (twoSidedSingularProjection S (Ahat - A)) +
          2 * matrixInner (noiseMatrix P X Y ω) (Ahat - A) := by sorry

end KLTNuclear.Oracle
