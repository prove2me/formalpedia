-- Prove2me | Theorems.Thm_KLTNuclear_RestrictedEigen_eq_2_20
-- name    : KLTNuclear.RestrictedEigen.eq_2_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:41:32.08282+00:00
-- url     : https://prove2.me/theorems/51f11fce-972b-469a-a8fd-1d96a1d2c1d0
-- title:
--   (2.20) — when ⟨Â−A₀, Â−A⟩_{L₂(Π)} > 0, the normal part of Â is controlled by the tangent part of Â − A
-- statement:
--   Work in the trace regression model with $n \ge 1$ observations. Let $\mathbb A$ be a linear subspace of $\mathbb R^{m_1\times m_2}$, let $\lambda > 0$, and let $\hat A^\lambda$ minimize $L_n$ over $\mathbb A$. Let $A \in \mathbb A$ have support $(S_1, S_2)$ and suppose that
--   $$
--   \langle \hat A^\lambda - A_0, \hat A^\lambda - A\rangle_{L_2(\Pi)} > 0.
--   $$
--   Then
--   $$
--   \lambda \|P_{S_1^\perp}\hat A^\lambda P_{S_2^\perp}\|_1 \le \lambda \|\mathcal P_A(\hat A^\lambda - A)\|_1 + 2\langle \mathbf M, \hat A^\lambda - A\rangle.
--   $$
--
--   This is the first step of the proof of Theorem 2 in the case that is not settled by the identity (2.9). It is the starting point for showing that $\hat A^\lambda - A$ lies in the cone $\mathbb C_{A,5}$.
--
--   **Formalization Note** The statement holds at every outcome $\omega$. $\mathcal P_A$ is `tangentProjection S` for an SVD `S` of $A$. The case hypothesis is a hypothesis of the statement, as on the page.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 11, (2.20) (proof of Theorem 2)

import Mathlib
import Definitions.Def_KLTNuclear_RestrictedEigen_Model

open MeasureTheory MatrixCompletion

namespace KLTNuclear.RestrictedEigen

/-- (2.20), proof of Theorem 2, arXiv:1011.6256v4, p. 11. In the trace regression model (1.1)
with `n ≥ 1` observations, let `𝔸` be a linear subspace of ℝ^{m₁×m₂}, `λ > 0`, and let `Â` be a
minimizer of `L_n` over `𝔸` at the outcome `ω`. Let `A ∈ 𝔸` have SVD `S` (support (S₁, S₂)).
If ⟨Â − A₀, Â − A⟩_{L₂(Π)} > 0, then
λ‖P_{S₁⊥} Â P_{S₂⊥}‖₁ ≤ λ‖𝒫_A(Â − A)‖₁ + 2⟨M, Â − A⟩.
Formalization Note: 𝒫_A is `tangentProjection S`, P_{S₁⊥} Â P_{S₂⊥} is `normalProjection S Â`,
**M** is `noiseMatrix P X Y ω` of (2.2). The case hypothesis is part of the statement, as on
the page. -/
theorem eq_2_20 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n) {X : Fin n → Ω → RealMatrix m₁ m₂} {Y : Fin n → Ω → ℝ}
    {A₀ : RealMatrix m₁ m₂} (hmodel : TraceRegression P X Y A₀)
    (𝔸 : Submodule ℝ (RealMatrix m₁ m₂)) {lam : ℝ} (hlam : 0 < lam) (ω : Ω)
    {Ahat : RealMatrix m₁ m₂} (hAhat : IsEstimator P X Y (𝔸 : Set (RealMatrix m₁ m₂)) lam ω Ahat)
    {A : RealMatrix m₁ m₂} (hA : A ∈ 𝔸) {r : ℕ} (S : SVD A r)
    (hcase : 0 < KLTNuclear.Oracle.l2Inner P X (Ahat - A₀) (Ahat - A)) :
    lam * nuclearNorm (normalProjection S Ahat) ≤
      lam * nuclearNorm (tangentProjection S (Ahat - A)) +
        2 * matrixInner (KLTNuclear.Oracle.noiseMatrix P X Y ω) (Ahat - A) := by sorry

end KLTNuclear.RestrictedEigen
