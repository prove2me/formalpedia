-- Prove2me | Theorems.Thm_LpSubspaceCoreset_SmallP_lemma_2_6_xi_le_one
-- name    : LpSubspaceCoreset.SmallP.lemma_2_6_xi_le_one
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:18:16.49092+00:00
-- url     : https://prove2.me/theorems/e9c036de-e07d-469c-b471-1db7a8530447
-- title:
--   Lemma 2.6 with 0 ≤ ξ₁ ≤ 1 (corrected: the printed lower bound fails for ξ₁ > 1)
-- statement:
--   Source (Lemma 2.6, p. 10): if $A_0=S_0A$ is a $(1\pm\xi_0)$ strong row coreset for $A$ and $A_1=S_1A_0$ is a $(1\pm\xi_1)$ strong row coreset for $A_0$, then for every $F\in\mathcal F_k$, $(1-\xi_0)(1-\xi_1)\,\mathrm{cost}_A(F)\le\mathrm{cost}_{A_1}(F)\le(1+\xi_0)(1+\xi_1)\,\mathrm{cost}_A(F)$; for $0<\varepsilon<1/2$ and $\xi_0=\xi_1=\varepsilon/3$, $A_1$ is a $(1\pm\varepsilon)$ strong row coreset for $A$; and $S_1S_0$ is a row-sampling matrix. Variant: the same conclusions under the additional hypothesis $0\le\xi_1\le1$. Difference: the source places no range on $\xi_1$, and at $\xi_0=\xi_1=3$ its first lower bound fails (evidence above).
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), p. 10, Lemma 2.6 (corrected)

import Mathlib
import Definitions.Def_LpSubspaceCoreset_SmallP_Cost

theorem LpSubspaceCoreset.SmallP.lemma_2_6_xi_le_one (p : ℝ) (k : ℕ) {n d s₀ s₁ : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ)
    (S₀ : Matrix (Fin s₀) (Fin n) ℝ) (S₁ : Matrix (Fin s₁) (Fin s₀) ℝ) (ξ₀ ξ₁ : ℝ)
    (hξ₁ : 0 ≤ ξ₁) (hξ₁' : ξ₁ ≤ 1)
    (h₀ : LpSubspaceCoreset.SmallP.IsStrongCoreset p k ξ₀ A S₀)
    (h₁ : LpSubspaceCoreset.SmallP.IsStrongCoreset p k ξ₁ (S₀ * A) S₁) :
    (∀ F : Submodule ℝ (EuclideanSpace ℝ (Fin d)), LpSubspaceCoreset.SmallP.InFk k F →
      (1 - ξ₀) * (1 - ξ₁) * LpSubspaceCoreset.SmallP.cost p A F ≤
          LpSubspaceCoreset.SmallP.cost p (S₁ * (S₀ * A)) F ∧
        LpSubspaceCoreset.SmallP.cost p (S₁ * (S₀ * A)) F ≤
          (1 + ξ₀) * (1 + ξ₁) * LpSubspaceCoreset.SmallP.cost p A F) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ξ₀ = ε / 3 → ξ₁ = ε / 3 →
      LpSubspaceCoreset.SmallP.IsStrongCoreset p k ε A (S₁ * S₀)) ∧
    LpSubspaceCoreset.SmallP.IsRowSampling (S₁ * S₀) := by sorry
