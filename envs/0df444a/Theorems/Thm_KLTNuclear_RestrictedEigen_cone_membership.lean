-- Prove2me | Theorems.Thm_KLTNuclear_RestrictedEigen_cone_membership
-- name    : KLTNuclear.RestrictedEigen.cone_membership
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:42:25.320119+00:00
-- url     : https://prove2.me/theorems/cd44e76f-135f-43dd-b465-1e842fc52b19
-- title:
--   Proof of Theorem 2, p. 11 — for λ ≥ 3Δ, Â − A ∈ ℂ_{A,5} and ‖𝒫_A(Â − A)‖₂ ≤ μ(A)‖Â − A‖_{L₂(Π)}
-- statement:
--   Work in the trace regression model with $n \ge 1$ observations. Let $\mathbb A$ be a linear subspace of $\mathbb R^{m_1\times m_2}$, let $\lambda > 0$ with $\lambda \ge 3\Delta$, where $\Delta = \|\mathbf M\|_\infty$, and let $\hat A^\lambda$ minimize $L_n$ over $\mathbb A$. Let $A \in \mathbb A$ have support $(S_1, S_2)$ and suppose $\langle \hat A^\lambda - A_0, \hat A^\lambda - A\rangle_{L_2(\Pi)} > 0$. Then:
--
--   1. $\|\mathcal P_A^\perp(\hat A^\lambda - A)\|_1 \le 5\|\mathcal P_A(\hat A^\lambda - A)\|_1$;
--   2. $\hat A^\lambda - A \in \mathbb C_{A,5}$;
--   3. for every cone constant $\mu'$ for $(A, 5)$,
--   $$
--   \|\mathcal P_A(\hat A^\lambda - A)\|_2 \le \mu'\,\|\hat A^\lambda - A\|_{L_2(\Pi)}.
--   $$
--
--   The third item is the inequality $\|\mathcal P_A(\hat A^\lambda - A)\|_2 \le \mu(A)\|\hat A^\lambda - A\|_{L_2(\Pi)}$ of the page with $\mu(A) = \mu_5(A)$. It is where the restricted constant replaces the global isometry Assumption 1 of Theorem 1. The constant $5 = (\lambda + 2\Delta)/(\lambda - 2\Delta)$ at $\lambda = 3\Delta$ comes from (2.22).
--
--   **Formalization Note** The statement holds at every outcome $\omega$. The third item is stated for every cone constant (see the definition `ConeConstant`) instead of the infimum $\mu(A)$; the two forms are equivalent, and the witness form avoids the junk value $0$ of a real infimum of an empty set. $\|B\|_{L_2(\Pi)}$ is the square root of `l2NormSq`.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 11, proof of Theorem 2, display after (2.22) and the sentence following it

import Mathlib
import Definitions.Def_KLTNuclear_RestrictedEigen_ConeConstant

open MeasureTheory MatrixCompletion

namespace KLTNuclear.RestrictedEigen

/-- Proof of Theorem 2, arXiv:1011.6256v4, p. 11, display after (2.22). In the trace regression
model (1.1) with `n ≥ 1` observations, let `𝔸` be a linear subspace of ℝ^{m₁×m₂}, `λ > 0` with
λ ≥ 3Δ where Δ = ‖M‖∞, and let `Â` be a minimizer of `L_n` over `𝔸` at the outcome `ω`. Let
`A ∈ 𝔸` have SVD `S`. If ⟨Â − A₀, Â − A⟩_{L₂(Π)} > 0, then
‖𝒫_A⊥(Â − A)‖₁ ≤ 5‖𝒫_A(Â − A)‖₁, hence Â − A ∈ ℂ_{A,5}, and thus
‖𝒫_A(Â − A)‖₂ ≤ μ(A)‖Â − A‖_{L₂(Π)}.
Formalization Note: μ(A) = μ₅(A) is the infimum of the constants `μ'` with
`IsConeConstant P X 𝔸 S 5 μ'`; the last conclusion is stated for every such `μ'`, which is
equivalent to the bound with the infimum (and empty when there is no such `μ'`, where the
paper's μ(A) = +∞). ‖·‖_{L₂(Π)} is the square root of `l2NormSq`. -/
theorem cone_membership {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n) {X : Fin n → Ω → RealMatrix m₁ m₂} {Y : Fin n → Ω → ℝ}
    {A₀ : RealMatrix m₁ m₂} (hmodel : TraceRegression P X Y A₀)
    (𝔸 : Submodule ℝ (RealMatrix m₁ m₂)) {lam : ℝ} (hlam : 0 < lam) (ω : Ω)
    (h3 : 3 * spectralNorm (KLTNuclear.Oracle.noiseMatrix P X Y ω) ≤ lam)
    {Ahat : RealMatrix m₁ m₂} (hAhat : IsEstimator P X Y (𝔸 : Set (RealMatrix m₁ m₂)) lam ω Ahat)
    {A : RealMatrix m₁ m₂} (hA : A ∈ 𝔸) {r : ℕ} (S : SVD A r)
    (hcase : 0 < KLTNuclear.Oracle.l2Inner P X (Ahat - A₀) (Ahat - A)) :
    nuclearNorm (normalProjection S (Ahat - A)) ≤ 5 * nuclearNorm (tangentProjection S (Ahat - A)) ∧
      Ahat - A ∈ cone 𝔸 S 5 ∧
      ∀ μ' : ℝ, IsConeConstant P X 𝔸 S 5 μ' →
        frobeniusNorm (tangentProjection S (Ahat - A)) ≤
          μ' * Real.sqrt (KLTNuclear.Oracle.l2NormSq P X (Ahat - A)) := by sorry

end KLTNuclear.RestrictedEigen
