-- Prove2me | Theorems.Thm_KLTNuclear_RestrictedEigen_theorem_2
-- name    : KLTNuclear.RestrictedEigen.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:32.187177+00:00
-- url     : https://prove2.me/theorems/7eefb709-047b-46b9-b5ff-0ba88e88798c
-- title:
--   Theorem 2 — on a linear subspace with λ ≥ 3‖M‖∞, the sharp oracle inequality (2.19) with λ²μ²(A)rank(A)
-- statement:
--   Work in the trace regression model $\mathbb E(Y_i\mid X_i) = \operatorname{tr}(X_i^\top A_0)$ with $n \ge 1$ observations. Let $\mathbb A$ be a linear subspace of $\mathbb R^{m_1\times m_2}$, let $\lambda > 0$, and let $\hat A^\lambda$ be a minimizer over $\mathbb A$ of
--   $$
--   L_n(A) = \|A\|_{L_2(\Pi)}^2 - \Big\langle \frac2n\sum_{i=1}^n Y_iX_i, A\Big\rangle + \lambda\|A\|_1 .
--   $$
--   Let $\mathbf M = \frac1n\sum_{i=1}^n (Y_iX_i - \mathbb E(Y_iX_i))$. If $\lambda \ge 3\|\mathbf M\|_\infty$, then
--   $$
--   \|\hat A^\lambda - A_0\|_{L_2(\Pi)}^2 \le \inf_{A \in \mathbb A}\Big[\|A - A_0\|_{L_2(\Pi)}^2 + \lambda^2\mu^2(A)\operatorname{rank}(A)\Big],
--   $$
--   where $\mu(A) = \mu_5(A)$ is the restricted constant of the cone $\mathbb C_{A,5}$.
--
--   This is a sharp oracle inequality (leading constant $1$) that replaces the global isometry Assumption 1 of Theorem 1 by a condition only on the cone of matrices that are approximately low-rank around $A$, in the manner of the restricted eigenvalue condition for the Lasso. The matrix $A_0$ need not belong to $\mathbb A$.
--
--   **Formalization Note** The infimum is unfolded to a bound for every $A \in \mathbb A$. The quantity $\mu(A)$ is an infimum that may be $+\infty$; the bound is stated for every cone constant $\mu'$ for $(A, 5)$ (see `ConeConstant`), which is equivalent and avoids the junk value $0$ of a real infimum of an empty set. The support of $A$ enters through an arbitrary SVD `S` of $A$. The statement is deterministic: it holds at every outcome $\omega$ at which $\lambda \ge 3\|\mathbf M\|_\infty$. The model assumptions, including the integrability conditions the page leaves implicit, are those of `TraceRegression`.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 11, Theorem 2, (2.19)

import Mathlib
import Definitions.Def_KLTNuclear_RestrictedEigen_ConeConstant

open MeasureTheory MatrixCompletion

namespace KLTNuclear.RestrictedEigen

/-- Theorem 2, arXiv:1011.6256v4, p. 11, (2.19). In the trace regression model (1.1) with
`n ≥ 1` observations, let `𝔸` be a linear subspace of ℝ^{m₁×m₂}, `λ > 0`, and let `Â` be a
minimizer of `L_n` over `𝔸` at the outcome `ω`. If λ ≥ 3‖M‖∞, then
‖Â − A₀‖²_{L₂(Π)} ≤ inf_{A ∈ 𝔸} [‖A − A₀‖²_{L₂(Π)} + λ² μ²(A) rank(A)].
Formalization Note: the infimum is unfolded to "for every `A ∈ 𝔸`"; μ(A) = μ₅(A) is the
infimum of the constants `μ'` with `IsConeConstant P X 𝔸 S 5 μ'` (`S` an SVD of `A`), and the
bound is stated for every such `μ'` (equivalent to the infimum form; vacuous when μ(A) = +∞).
The statement is realization-wise: it holds at every outcome `ω` with λ ≥ 3‖M‖∞. `A₀` need not
lie in `𝔸`. -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n) {X : Fin n → Ω → RealMatrix m₁ m₂} {Y : Fin n → Ω → ℝ}
    {A₀ : RealMatrix m₁ m₂} (hmodel : TraceRegression P X Y A₀)
    (𝔸 : Submodule ℝ (RealMatrix m₁ m₂)) {lam : ℝ} (hlam : 0 < lam) (ω : Ω)
    (h3 : 3 * spectralNorm (KLTNuclear.Oracle.noiseMatrix P X Y ω) ≤ lam)
    {Ahat : RealMatrix m₁ m₂} (hAhat : IsEstimator P X Y (𝔸 : Set (RealMatrix m₁ m₂)) lam ω Ahat) :
    ∀ A ∈ 𝔸, ∀ (r : ℕ) (S : SVD A r) (μ' : ℝ), IsConeConstant P X 𝔸 S 5 μ' →
      KLTNuclear.Oracle.l2NormSq P X (Ahat - A₀) ≤ KLTNuclear.Oracle.l2NormSq P X (A - A₀) + lam ^ 2 * μ' ^ 2 * (A.rank : ℝ) := by sorry

end KLTNuclear.RestrictedEigen
