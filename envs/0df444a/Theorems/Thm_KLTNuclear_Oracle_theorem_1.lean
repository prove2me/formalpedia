-- Prove2me | Theorems.Thm_KLTNuclear_Oracle_theorem_1
-- name    : KLTNuclear.Oracle.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:20.276395+00:00
-- url     : https://prove2.me/theorems/9946ce0a-b64c-4973-97ab-fd78a143c6b2
-- title:
--   Theorem 1 — sharp oracle inequalities (2.3)–(2.5) for the nuclear-norm penalized estimator when $\lambda\ge2\|\mathbf M\|_\infty$
-- statement:
--   Let $(X_i,Y_i)$, $i=1,\dots,n$ ($n\ge1$), follow the trace regression model
--   $$\mathbb E(Y_i\mid X_i)=\langle A_0,X_i\rangle=\operatorname{tr}(X_i^\top A_0),$$
--   where $X_i$ are random real $m_1\times m_2$ matrices with square-integrable entries, $Y_i$ are integrable real random variables with $Y_i(X_i)_{jk}$ integrable, and $A_0$ is a fixed matrix. Let $\mathbb A$ be a set of $m_1\times m_2$ matrices and $\lambda>0$. Fix a realization of the sample and let $\hat A^\lambda$ be a minimizer over $\mathbb A$ of
--   $$L_n(A)=\|A\|^2_{L_2(\Pi)}-\Big\langle\frac2n\sum_{i=1}^nY_iX_i,A\Big\rangle+\lambda\|A\|_1,$$
--   where $\|A\|^2_{L_2(\Pi)}=\frac1n\sum_i\mathbb E\langle A,X_i\rangle^2$ and $\|\cdot\|_1$ is the nuclear norm. Let $\mathbf M=\frac1n\sum_{i=1}^n(Y_iX_i-\mathbb E(Y_iX_i))$ and suppose $\lambda\ge2\|\mathbf M\|_\infty$ (operator norm). Then:
--
--   1. for any set $\mathbb A$,
--   $$\|\hat A^\lambda-A_0\|^2_{L_2(\Pi)}\le\inf_{A\in\mathbb A}\Big[\|A-A_0\|^2_{L_2(\Pi)}+2\lambda\|A\|_1\Big];\qquad(2.3)$$
--   2. if, in addition, $\mathbb A$ is convex and Assumption 1 holds with a constant $\mu>0$ (that is, $\|D\|^2_{L_2(\Pi)}\ge\mu^{-2}\|D\|_2^2$ for all $D\in\mathbb A-\mathbb A$), then
--   $$\|\hat A^\lambda-A_0\|^2_{L_2(\Pi)}\le\inf_{A\in\mathbb A}\Big[\|A-A_0\|^2_{L_2(\Pi)}+\Big(\frac{1+\sqrt2}{2}\Big)^2\mu^2\lambda^2\operatorname{rank}(A)\Big];\qquad(2.4)$$
--   3. in this case, for every $A\in\mathbb A$ with support $(S_1,S_2)$,
--   $$\|\hat A^\lambda-A_0\|^2_{L_2(\Pi)}+(\lambda-2\|\mathbf M\|_\infty)\|P_{S_1^\perp}\hat A^\lambda P_{S_2^\perp}\|_1\le\|A-A_0\|^2_{L_2(\Pi)}+\Big(\frac{1+\sqrt2}{2}\Big)^2\mu^2\lambda^2\operatorname{rank}(A).\qquad(2.5)$$
--
--   These are sharp oracle inequalities: the leading constant in front of the approximation error $\|A-A_0\|^2_{L_2(\Pi)}$ is $1$. The first is the "slow rate" bound in terms of the nuclear norm of the oracle, the second the "fast rate" bound in terms of its rank. Every later upper bound of the paper (matrix completion, Theorem 4) is obtained by bounding $\|\mathbf M\|_\infty$ in probability and applying this theorem.
--
--   **Formalization Note** The statement is realization-wise: it holds for every sample point at which $\hat A^\lambda$ is a minimizer and $\lambda\ge2\|\mathbf M\|_\infty$. Each infimum is stated as the bound for every $A\in\mathbb A$ (equivalent). The model (1.1) is the conditional expectation of $Y_i$ given the $\sigma$-algebra of the entries of $X_i$. The integrability and measurability conditions are not printed in the paper; they make the expectations meaningful. Independence of the pairs is not assumed (the proof does not use it). The support $(S_1,S_2)$ is given by SVD data `S : SVD A r`, and $P_{S_1^\perp}\hat A^\lambda P_{S_2^\perp}$ is `normalProjection S Ahat`.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 6, Theorem 1, (2.3)–(2.5)

import Mathlib
import Definitions.Def_KLTNuclear_Oracle_Model

open MeasureTheory MatrixCompletion

namespace KLTNuclear.Oracle

/-- Theorem 1 (p. 6), (2.3)–(2.5). -/
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → RealMatrix m₁ m₂) (Y : Fin n → Ω → ℝ)
    (hreg : SampleRegularity P X Y)
    (A₀ : RealMatrix m₁ m₂) (hmodel : TraceRegressionModel P X Y A₀)
    (𝔸 : Set (RealMatrix m₁ m₂)) (lam : ℝ) (hlam : 0 < lam)
    (ω : Ω) (Ahat : RealMatrix m₁ m₂) (hAhat : IsEstimator P X Y lam ω 𝔸 Ahat)
    (hM : 2 * spectralNorm (noiseMatrix P X Y ω) ≤ lam) :
    -- (2.3), for any set 𝔸
    (∀ A ∈ 𝔸, l2NormSq P X (Ahat - A₀) ≤ l2NormSq P X (A - A₀) + 2 * lam * nuclearNorm A) ∧
    (Convex ℝ 𝔸 → ∀ μ : ℝ, Assumption1 P X 𝔸 μ →
      -- (2.4)
      (∀ A ∈ 𝔸, l2NormSq P X (Ahat - A₀) ≤
          l2NormSq P X (A - A₀) + ((1 + Real.sqrt 2) / 2) ^ 2 * μ ^ 2 * lam ^ 2 * (A.rank : ℝ)) ∧
      -- (2.5), for every A ∈ 𝔸 with support (S₁, S₂) given by an SVD S of A
      (∀ A ∈ 𝔸, ∀ (r : ℕ) (S : SVD A r),
        l2NormSq P X (Ahat - A₀) +
            (lam - 2 * spectralNorm (noiseMatrix P X Y ω)) * nuclearNorm (normalProjection S Ahat) ≤
          l2NormSq P X (A - A₀) + ((1 + Real.sqrt 2) / 2) ^ 2 * μ ^ 2 * lam ^ 2 * (A.rank : ℝ))) := by sorry

end KLTNuclear.Oracle
