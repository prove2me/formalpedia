-- Prove2me | Theorems.Thm_KLTNuclear_Oracle_eq_2_3
-- name    : KLTNuclear.Oracle.eq_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:32.38575+00:00
-- url     : https://prove2.me/theorems/f3e11ac8-d1eb-4bb5-bde1-530816d49483
-- title:
--   Theorem 1 (2.3) — if $\lambda\ge2\|\mathbf M\|_\infty$, $\|\hat A^\lambda-A_0\|^2_{L_2(\Pi)}\le\inf_{A\in\mathbb A}[\|A-A_0\|^2_{L_2(\Pi)}+2\lambda\|A\|_1]$
-- statement:
--   In the trace regression model $\mathbb E(Y_i\mid X_i)=\langle A_0,X_i\rangle$ with square-integrable design entries and integrable responses, let $\mathbb A$ be **any** set of $m_1\times m_2$ matrices, $\lambda>0$, and fix a realization of the sample at which $\hat A^\lambda$ minimizes the penalized empirical risk $L_n$ over $\mathbb A$. If
--   $$\lambda\ge2\|\mathbf M\|_\infty,\qquad \mathbf M=\frac1n\sum_{i=1}^n\big(Y_iX_i-\mathbb E(Y_iX_i)\big),$$
--   then
--   $$\|\hat A^\lambda-A_0\|^2_{L_2(\Pi)}\le\inf_{A\in\mathbb A}\Big[\|A-A_0\|^2_{L_2(\Pi)}+2\lambda\|A\|_1\Big].$$
--
--   This is the "slow rate" half of Theorem 1: a sharp oracle inequality (leading constant 1) with the nuclear-norm penalty as remainder, valid without convexity of $\mathbb A$ or any assumption on the design.
--
--   **Formalization Note** The infimum is stated as the bound for every $A\in\mathbb A$, which is equivalent. Model hypothesis in conditional-expectation form; integrability conditions added as in the definition module; independence not assumed.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 6, Theorem 1, (2.3)

import Mathlib
import Definitions.Def_KLTNuclear_Oracle_Model

open MeasureTheory MatrixCompletion

namespace KLTNuclear.Oracle

/-- (2.3) of Theorem 1 (p. 6): any set 𝔸, λ ≥ 2‖𝐌‖∞. -/
theorem eq_2_3 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → RealMatrix m₁ m₂) (Y : Fin n → Ω → ℝ)
    (hreg : SampleRegularity P X Y)
    (A₀ : RealMatrix m₁ m₂) (hmodel : TraceRegressionModel P X Y A₀)
    (𝔸 : Set (RealMatrix m₁ m₂)) (lam : ℝ) (hlam : 0 < lam)
    (ω : Ω) (Ahat : RealMatrix m₁ m₂) (hAhat : IsEstimator P X Y lam ω 𝔸 Ahat)
    (hM : 2 * spectralNorm (noiseMatrix P X Y ω) ≤ lam) :
    ∀ A ∈ 𝔸, l2NormSq P X (Ahat - A₀) ≤ l2NormSq P X (A - A₀) + 2 * lam * nuclearNorm A := by sorry

end KLTNuclear.Oracle
