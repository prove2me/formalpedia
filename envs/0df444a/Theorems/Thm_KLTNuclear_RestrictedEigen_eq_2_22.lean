-- Prove2me | Theorems.Thm_KLTNuclear_RestrictedEigen_eq_2_22
-- name    : KLTNuclear.RestrictedEigen.eq_2_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:42:19.211523+00:00
-- url     : https://prove2.me/theorems/df95c5fd-4e21-49b0-ab2f-a9db45a4a462
-- title:
--   (2.22) — (λ − 2Δ)‖𝒫_A⊥(Â − A)‖₁ ≤ (λ + 2Δ)‖𝒫_A(Â − A)‖₁
-- statement:
--   Work in the trace regression model with $n \ge 1$ observations. Let $\mathbb A$ be a linear subspace of $\mathbb R^{m_1\times m_2}$, let $\lambda > 0$, and let $\hat A^\lambda$ minimize $L_n$ over $\mathbb A$. Write $\Delta = \|\mathbf M\|_\infty$. Let $A \in \mathbb A$ have support $(S_1, S_2)$ and suppose $\langle \hat A^\lambda - A_0, \hat A^\lambda - A\rangle_{L_2(\Pi)} > 0$. Then
--   $$
--   (\lambda - 2\Delta)\|\mathcal P_A^\perp(\hat A^\lambda - A)\|_1 \le (\lambda + 2\Delta)\|\mathcal P_A(\hat A^\lambda - A)\|_1.
--   $$
--
--   Combined with $\lambda \ge 3\Delta$, this inequality puts $\hat A^\lambda - A$ into the cone $\mathbb C_{A,5}$.
--
--   **Formalization Note** The statement holds at every outcome $\omega$. $\Delta$ is the operator norm `spectralNorm` of the noise matrix of (2.2). No lower bound on $\lambda$ beyond $\lambda > 0$ is assumed, as on the page.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 11, (2.22) (proof of Theorem 2)

import Mathlib
import Definitions.Def_KLTNuclear_RestrictedEigen_Model

open MeasureTheory MatrixCompletion

namespace KLTNuclear.RestrictedEigen

/-- (2.22), proof of Theorem 2, arXiv:1011.6256v4, p. 11. In the trace regression model (1.1)
with `n ≥ 1` observations, let `𝔸` be a linear subspace of ℝ^{m₁×m₂}, `λ > 0`, and let `Â` be a
minimizer of `L_n` over `𝔸` at the outcome `ω`. Let `A ∈ 𝔸` have SVD `S` and write
Δ = ‖M‖∞. If ⟨Â − A₀, Â − A⟩_{L₂(Π)} > 0, then
(λ − 2Δ)‖𝒫_A⊥(Â − A)‖₁ ≤ (λ + 2Δ)‖𝒫_A(Â − A)‖₁.
Formalization Note: 𝒫_A is `tangentProjection S`, 𝒫_A⊥ is `normalProjection S`, Δ is
`spectralNorm (KLTNuclear.Oracle.noiseMatrix P X Y ω)` (the operator norm of **M** of (2.2)). -/
theorem eq_2_22 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n) {X : Fin n → Ω → RealMatrix m₁ m₂} {Y : Fin n → Ω → ℝ}
    {A₀ : RealMatrix m₁ m₂} (hmodel : TraceRegression P X Y A₀)
    (𝔸 : Submodule ℝ (RealMatrix m₁ m₂)) {lam : ℝ} (hlam : 0 < lam) (ω : Ω)
    {Ahat : RealMatrix m₁ m₂} (hAhat : IsEstimator P X Y (𝔸 : Set (RealMatrix m₁ m₂)) lam ω Ahat)
    {A : RealMatrix m₁ m₂} (hA : A ∈ 𝔸) {r : ℕ} (S : SVD A r)
    (hcase : 0 < KLTNuclear.Oracle.l2Inner P X (Ahat - A₀) (Ahat - A)) :
    (lam - 2 * spectralNorm (KLTNuclear.Oracle.noiseMatrix P X Y ω)) * nuclearNorm (normalProjection S (Ahat - A)) ≤
      (lam + 2 * spectralNorm (KLTNuclear.Oracle.noiseMatrix P X Y ω)) *
        nuclearNorm (tangentProjection S (Ahat - A)) := by sorry

end KLTNuclear.RestrictedEigen
