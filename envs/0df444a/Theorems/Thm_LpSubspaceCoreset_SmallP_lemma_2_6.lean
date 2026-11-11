-- Prove2me | Theorems.Thm_LpSubspaceCoreset_SmallP_lemma_2_6
-- name    : LpSubspaceCoreset.SmallP.lemma_2_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:47:24.500267+00:00
-- url     : https://prove2.me/theorems/d723355a-b019-4fd9-b987-bbd81d8a9355
-- title:
--   Lemma 2.6 — composing two strong row coresets
-- statement:
--   Let $p$ and $k$ be fixed, $A\in\mathbb R^{n\times d}$, and let $S_0\in\mathbb R^{s_0\times n}$, $S_1\in\mathbb R^{s_1\times s_0}$ be reweighted row subsets (one nonzero entry per row). Suppose $A_0=S_0A$ is a $(1\pm\xi_0)$ strong row coreset of $A$ and $A_1=S_1A_0$ is a $(1\pm\xi_1)$ strong row coreset of $A_0$ (as printed, no range is placed on $\xi_0,\xi_1$). Then for every subspace $F$ of dimension at most $k$,
--   $$(1-\xi_0)(1-\xi_1)\,\mathrm{cost}_A(F)\le\mathrm{cost}_{A_1}(F)\le(1+\xi_0)(1+\xi_1)\,\mathrm{cost}_A(F).$$
--   If moreover $0<\varepsilon<1/2$ and $\xi_0=\xi_1=\varepsilon/3$, then $A_1=(S_1S_0)A$ is a $(1\pm\varepsilon)$ strong row coreset of $A$; and $S_1S_0$ is again a row-sampling matrix for the original rows of $A$.
--
--   This is how the main theorem chains the Woodruff–Yasuda pre-sparsification with the low-rank-split sampling.
--
--   Differences from the source: none.
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), p. 10, Lemma 2.6

import Mathlib
import Definitions.Def_LpSubspaceCoreset_SmallP_Cost

namespace LpSubspaceCoreset.SmallP

/-- **Lemma 2.6** (Composition of strong row coresets), p. 10.

If `A₀ = S₀A` is a `(1 ± ξ₀)` strong row coreset for `A` and `A₁ = S₁A₀` is a `(1 ± ξ₁)` strong row
coreset for `A₀`, then for every `F` with `dim F ≤ k`,
`(1 − ξ₀)(1 − ξ₁) cost_A(F) ≤ cost_{A₁}(F) ≤ (1 + ξ₀)(1 + ξ₁) cost_A(F)`; if `0 < ε < 1/2` and
`ξ₀ = ξ₁ = ε/3`, then `A₁ = (S₁S₀)A` is a `(1 ± ε)` strong row coreset for `A`; and `S₁S₀` is again
a row-sampling matrix. As printed, no range is placed on `ξ₀, ξ₁`. -/
theorem lemma_2_6 (p : ℝ) (k : ℕ) {n d s₀ s₁ : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (S₀ : Matrix (Fin s₀) (Fin n) ℝ) (S₁ : Matrix (Fin s₁) (Fin s₀) ℝ) (ξ₀ ξ₁ : ℝ)
    (h₀ : IsStrongCoreset p k ξ₀ A S₀) (h₁ : IsStrongCoreset p k ξ₁ (S₀ * A) S₁) :
    (∀ F : Submodule ℝ (EuclideanSpace ℝ (Fin d)), InFk k F →
      (1 - ξ₀) * (1 - ξ₁) * cost p A F ≤ cost p (S₁ * (S₀ * A)) F ∧
        cost p (S₁ * (S₀ * A)) F ≤ (1 + ξ₀) * (1 + ξ₁) * cost p A F) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ξ₀ = ε / 3 → ξ₁ = ε / 3 →
      IsStrongCoreset p k ε A (S₁ * S₀)) ∧
    IsRowSampling (S₁ * S₀) := by sorry

end LpSubspaceCoreset.SmallP
