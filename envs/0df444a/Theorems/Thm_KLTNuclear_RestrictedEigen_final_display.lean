-- Prove2me | Theorems.Thm_KLTNuclear_RestrictedEigen_final_display
-- name    : KLTNuclear.RestrictedEigen.final_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:42:46.548461+00:00
-- url     : https://prove2.me/theorems/1d1b5270-cd93-4335-94db-b62b838c3987
-- title:
--   Proof of Theorem 2, p. 11 — the final two-step bound with (1 + 2√2/3)μ(A)λ√rank(A)
-- statement:
--   Work in the trace regression model with $n \ge 1$ observations. Let $\mathbb A$ be a linear subspace of $\mathbb R^{m_1\times m_2}$, let $\lambda > 0$ with $\lambda \ge 3\|\mathbf M\|_\infty$, and let $\hat A^\lambda$ minimize $L_n$ over $\mathbb A$. Let $A \in \mathbb A$ have support $(S_1, S_2)$, suppose $\langle \hat A^\lambda - A_0, \hat A^\lambda - A\rangle_{L_2(\Pi)} > 0$, and let $\mu'$ be a cone constant for $(A, 5)$. Then
--   $$
--   \begin{aligned}
--   &\|\hat A^\lambda - A_0\|_{L_2(\Pi)}^2 + \|\hat A^\lambda - A\|_{L_2(\Pi)}^2 + \tfrac{\lambda}{3}\|P_{S_1^\perp}\hat A^\lambda P_{S_2^\perp}\|_1 \\
--   &\quad\le \|A - A_0\|_{L_2(\Pi)}^2 + \Big(1 + \tfrac{2\sqrt2}{3}\Big)\mu'\lambda\sqrt{\operatorname{rank}(A)}\,\|\hat A^\lambda - A\|_{L_2(\Pi)} \\
--   &\quad\le \|A - A_0\|_{L_2(\Pi)}^2 + \|\hat A^\lambda - A\|_{L_2(\Pi)}^2 + \mu'^2\lambda^2\operatorname{rank}(A).
--   \end{aligned}
--   $$
--
--   This is the last display of the proof of Theorem 2, with $\mu(A)$ replaced by any cone constant. Dropping the nonnegative terms $\|\hat A^\lambda - A\|^2_{L_2(\Pi)}$ and $\frac\lambda3\|P_{S_1^\perp}\hat A^\lambda P_{S_2^\perp}\|_1$ gives (2.19) in the case $\langle \hat A^\lambda - A_0, \hat A^\lambda - A\rangle_{L_2(\Pi)} > 0$.
--
--   **Formalization Note** The statement holds at every outcome $\omega$. Both inequalities are stated for every cone constant $\mu'$ in place of $\mu(A)$ (equivalent to the infimum form). $\|\cdot\|_{L_2(\Pi)}$ is the square root of `l2NormSq`, and the rank is `Matrix.rank` cast to $\mathbb R$.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 11, proof of Theorem 2, last display

import Mathlib
import Definitions.Def_KLTNuclear_RestrictedEigen_ConeConstant

open MeasureTheory MatrixCompletion

namespace KLTNuclear.RestrictedEigen

/-- Proof of Theorem 2, arXiv:1011.6256v4, p. 11, last display. In the trace regression model
(1.1) with `n ≥ 1` observations, let `𝔸` be a linear subspace of ℝ^{m₁×m₂}, `λ > 0` with
λ ≥ 3‖M‖∞, and let `Â` be a minimizer of `L_n` over `𝔸` at the outcome `ω`. Let `A ∈ 𝔸` have
SVD `S` and assume ⟨Â − A₀, Â − A⟩_{L₂(Π)} > 0. Then, for μ(A) = μ₅(A),
‖Â − A₀‖²_{L₂(Π)} + ‖Â − A‖²_{L₂(Π)} + (λ/3)‖P_{S₁⊥} Â P_{S₂⊥}‖₁
  ≤ ‖A − A₀‖²_{L₂(Π)} + (1 + 2√2/3) μ(A) λ √rank(A) ‖Â − A‖_{L₂(Π)}
  ≤ ‖A − A₀‖²_{L₂(Π)} + ‖Â − A‖²_{L₂(Π)} + μ²(A) λ² rank(A).
Formalization Note: both inequalities are stated for every `μ'` with
`IsConeConstant P X 𝔸 S 5 μ'` in place of μ(A) (equivalent to the infimum form; vacuous when
μ(A) = +∞). ‖·‖²_{L₂(Π)} is `l2NormSq`, ‖·‖_{L₂(Π)} its square root, and
P_{S₁⊥} Â P_{S₂⊥} is `normalProjection S Â`. The case hypothesis is the one under which the page
derives the display. -/
theorem final_display {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n) {X : Fin n → Ω → RealMatrix m₁ m₂} {Y : Fin n → Ω → ℝ}
    {A₀ : RealMatrix m₁ m₂} (hmodel : TraceRegression P X Y A₀)
    (𝔸 : Submodule ℝ (RealMatrix m₁ m₂)) {lam : ℝ} (hlam : 0 < lam) (ω : Ω)
    (h3 : 3 * spectralNorm (KLTNuclear.Oracle.noiseMatrix P X Y ω) ≤ lam)
    {Ahat : RealMatrix m₁ m₂} (hAhat : IsEstimator P X Y (𝔸 : Set (RealMatrix m₁ m₂)) lam ω Ahat)
    {A : RealMatrix m₁ m₂} (hA : A ∈ 𝔸) {r : ℕ} (S : SVD A r)
    (hcase : 0 < KLTNuclear.Oracle.l2Inner P X (Ahat - A₀) (Ahat - A))
    {μ' : ℝ} (hμ' : IsConeConstant P X 𝔸 S 5 μ') :
    KLTNuclear.Oracle.l2NormSq P X (Ahat - A₀) + KLTNuclear.Oracle.l2NormSq P X (Ahat - A) +
        (lam / 3) * nuclearNorm (normalProjection S Ahat) ≤
      KLTNuclear.Oracle.l2NormSq P X (A - A₀) +
        (1 + 2 * Real.sqrt 2 / 3) * μ' * lam * Real.sqrt (A.rank : ℝ) *
          Real.sqrt (KLTNuclear.Oracle.l2NormSq P X (Ahat - A)) ∧
    KLTNuclear.Oracle.l2NormSq P X (A - A₀) +
        (1 + 2 * Real.sqrt 2 / 3) * μ' * lam * Real.sqrt (A.rank : ℝ) *
          Real.sqrt (KLTNuclear.Oracle.l2NormSq P X (Ahat - A)) ≤
      KLTNuclear.Oracle.l2NormSq P X (A - A₀) + KLTNuclear.Oracle.l2NormSq P X (Ahat - A) + μ' ^ 2 * lam ^ 2 * (A.rank : ℝ) := by sorry

end KLTNuclear.RestrictedEigen
