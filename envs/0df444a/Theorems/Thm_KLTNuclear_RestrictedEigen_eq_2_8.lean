-- Prove2me | Theorems.Thm_KLTNuclear_RestrictedEigen_eq_2_8
-- name    : KLTNuclear.RestrictedEigen.eq_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:41:33.625347+00:00
-- url     : https://prove2.me/theorems/9a729c57-34d6-4dc7-b544-fa52708c8b97
-- title:
--   (2.8) — the basic inequality after the subgradient choice, for a convex domain
-- statement:
--   Work in the trace regression model with $n \ge 1$ observations. Let $\mathbb A$ be a convex set of $m_1 \times m_2$ matrices, let $\lambda > 0$, and let $\hat A^\lambda$ minimize $L_n$ over $\mathbb A$. Let $A \in \mathbb A$ have rank $r$ and singular value decomposition $A = \sum_{j=1}^r \sigma_j u_j v_j^\top$ with support $(S_1, S_2)$. Then
--   $$
--   2\langle \hat A^\lambda - A_0, \hat A^\lambda - A\rangle_{L_2(\Pi)} + \lambda \|P_{S_1^\perp}\hat A^\lambda P_{S_2^\perp}\|_1 \le -\lambda\Big\langle \sum_{j=1}^r u_j v_j^\top, \hat A^\lambda - A\Big\rangle + 2\langle \mathbf M, \hat A^\lambda - A\rangle.
--   $$
--
--   This is the inequality from which both Theorem 1 and Theorem 2 start. It combines the first-order optimality condition (2.6) of the estimator with the monotonicity of the subdifferential of the nuclear norm and a particular choice of subgradient at $A$.
--
--   **Formalization Note** The statement holds at every outcome $\omega$, with $\mathbf M$ and $\hat A^\lambda$ evaluated at $\omega$. $P_{S_1^\perp}\hat A^\lambda P_{S_2^\perp}$ is `normalProjection S Ahat` and $\sum_j u_jv_j^\top$ is `signMatrix S`. The page proves (2.8) inside the proof of Theorem 1, where $\mathbb A$ is convex; it is restated here because Theorem 2 reuses it.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 8, (2.8) (proof of Theorem 1; reused in the proof of Theorem 2, p. 11)

import Mathlib
import Definitions.Def_KLTNuclear_RestrictedEigen_Model

open MeasureTheory MatrixCompletion

namespace KLTNuclear.RestrictedEigen

/-- (2.8), proof of Theorem 1, arXiv:1011.6256v4, p. 8, reused in the proof of Theorem 2
(p. 11). In the trace regression model (1.1) with `n ≥ 1` observations, let `𝔸` be a convex
set of `m₁ × m₂` matrices, `λ > 0`, and let `Â` be a minimizer of `L_n` over `𝔸` at the
outcome `ω`. Then for every `A ∈ 𝔸` with SVD `S` (A = Σ_{j≤r} σ_j u_j v_jᵀ, support (S₁, S₂)),
2⟨Â − A₀, Â − A⟩_{L₂(Π)} + λ‖P_{S₁⊥} Â P_{S₂⊥}‖₁
  ≤ −λ⟨Σ_{j=1}^r u_j v_jᵀ, Â − A⟩ + 2⟨M, Â − A⟩.
Formalization Note: P_{S₁⊥} Â P_{S₂⊥} is `normalProjection S Â`, Σ u_j v_jᵀ is
`signMatrix S`, and **M** is `noiseMatrix P X Y ω` of (2.2). The statement is realization-wise:
it holds at every outcome `ω`. -/
theorem eq_2_8 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n) {X : Fin n → Ω → RealMatrix m₁ m₂} {Y : Fin n → Ω → ℝ}
    {A₀ : RealMatrix m₁ m₂} (hmodel : TraceRegression P X Y A₀)
    {𝔸 : Set (RealMatrix m₁ m₂)} (h𝔸 : Convex ℝ 𝔸) {lam : ℝ} (hlam : 0 < lam) (ω : Ω)
    {Ahat : RealMatrix m₁ m₂} (hAhat : IsEstimator P X Y 𝔸 lam ω Ahat)
    {A : RealMatrix m₁ m₂} (hA : A ∈ 𝔸) {r : ℕ} (S : SVD A r) :
    2 * KLTNuclear.Oracle.l2Inner P X (Ahat - A₀) (Ahat - A) + lam * nuclearNorm (normalProjection S Ahat) ≤
      -lam * matrixInner (signMatrix S) (Ahat - A) +
        2 * matrixInner (KLTNuclear.Oracle.noiseMatrix P X Y ω) (Ahat - A) := by sorry

end KLTNuclear.RestrictedEigen
