-- Prove2me | Theorems.Thm_KLTNuclear_Oracle_eq_2_17
-- name    : KLTNuclear.Oracle.eq_2_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:40.825769+00:00
-- url     : https://prove2.me/theorems/957d4e5b-7fd9-4767-a64c-fd8bacc52822
-- title:
--   (2.17) — the bound combining (2.11), (2.12), (2.16) and Assumption 1
-- statement:
--   Work in the trace regression model $\mathbb E(Y_i\mid X_i)=\langle A_0,X_i\rangle$ with square-integrable design entries and integrable responses. Let $\mathbb A$ be a **convex** set of $m_1\times m_2$ matrices satisfying Assumption 1 with constant $\mu>0$ ($\|D\|^2_{L_2(\Pi)}\ge\mu^{-2}\|D\|_2^2$ for $D\in\mathbb A-\mathbb A$), let $\lambda>0$, and fix a realization of the sample at which $\hat A^\lambda$ minimizes $L_n$ over $\mathbb A$; let $\mathbf M=\frac1n\sum_i(Y_iX_i-\mathbb E(Y_iX_i))$. For every $A\in\mathbb A$ with singular value decomposition $A=\sum_{j=1}^r\sigma_ju_jv_j^\top$ and support $(S_1,S_2)$, with
--   $$\Lambda=2\|\mathcal P_A(\mathbf M)\|_2,\qquad\Gamma=2\|P_{S_1^\perp}\mathbf MP_{S_2^\perp}\|_\infty,$$
--   one has
--   $$\|\hat A^\lambda-A_0\|^2_{L_2(\Pi)}+\|\hat A^\lambda-A\|^2_{L_2(\Pi)}+\lambda\|P_{S_1^\perp}\hat A^\lambda P_{S_2^\perp}\|_1\le\|A-A_0\|^2_{L_2(\Pi)}+\mu\big(\lambda\sqrt{\operatorname{rank}(A)}+\Lambda\big)\|\hat A^\lambda-A\|_{L_2(\Pi)}+\Gamma\|P_{S_1^\perp}\hat A^\lambda P_{S_2^\perp}\|_1 .$$
--
--   It is the last intermediate inequality of the proof of Theorem 1 before the fast-rate bounds (2.4) and (2.5).
--
--   **Formalization Note** $\|\cdot\|_{L_2(\Pi)}$ is the square root of $\|\cdot\|^2_{L_2(\Pi)}$. Model hypothesis in conditional-expectation form; integrability conditions added; independence not assumed.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 9, (2.17)

import Mathlib
import Definitions.Def_KLTNuclear_Oracle_Model

open MeasureTheory MatrixCompletion

namespace KLTNuclear.Oracle

/-- (2.17) (p. 9): for a convex 𝔸 under Assumption 1 with constant μ, every A ∈ 𝔸 with
support (S₁, S₂), Λ = 2‖𝒫_A(𝐌)‖₂ and Γ = 2‖P_{S₁⊥} 𝐌 P_{S₂⊥}‖∞. -/
theorem eq_2_17 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → RealMatrix m₁ m₂) (Y : Fin n → Ω → ℝ)
    (hreg : SampleRegularity P X Y)
    (A₀ : RealMatrix m₁ m₂) (hmodel : TraceRegressionModel P X Y A₀)
    (𝔸 : Set (RealMatrix m₁ m₂)) (h𝔸 : Convex ℝ 𝔸) (μ : ℝ) (hμ : Assumption1 P X 𝔸 μ)
    (lam : ℝ) (hlam : 0 < lam)
    (ω : Ω) (Ahat : RealMatrix m₁ m₂) (hAhat : IsEstimator P X Y lam ω 𝔸 Ahat) :
    ∀ A ∈ 𝔸, ∀ (r : ℕ) (S : SVD A r),
      l2NormSq P X (Ahat - A₀) + l2NormSq P X (Ahat - A) + lam * nuclearNorm (normalProjection S Ahat) ≤
        l2NormSq P X (A - A₀) +
          μ * (lam * Real.sqrt (A.rank : ℝ) +
              2 * frobeniusNorm (tangentProjection S (noiseMatrix P X Y ω))) * l2Norm P X (Ahat - A) +
          2 * spectralNorm (normalProjection S (noiseMatrix P X Y ω)) *
            nuclearNorm (normalProjection S Ahat) := by sorry

end KLTNuclear.Oracle
