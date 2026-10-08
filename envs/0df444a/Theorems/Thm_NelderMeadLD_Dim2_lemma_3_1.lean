-- Prove2me | Theorems.Thm_NelderMeadLD_Dim2_lemma_3_1
-- name    : NelderMeadLD.Dim2.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:14:56.599661+00:00
-- url     : https://prove2.me/theorems/af07f7fd-4373-4e88-a867-3070bc3cdf35
-- title:
--   Lemma 3.1, p. 120 — nondegeneracy is preserved; vol(Δₖ₊₁) = |τ| vol(Δₖ) after a step of type τ, = σⁿ vol(Δₖ) after a shrink
-- statement:
--   Let the coefficients satisfy (2.1), let $f:\mathbb R^n\to\mathbb R$ ($n\ge1$) be arbitrary, and let $(\Delta_k)$ be a run of Algorithm NM on $f$ from a nondegenerate initial simplex $\Delta_0$. Then
--   1. every simplex $\Delta_k$ is nondegenerate;
--   2. after a nonshrink iteration of type $\tau$ (the coefficient of the accepted point),
--   $$\operatorname{vol}(\Delta_{k+1})=|\tau|\,\operatorname{vol}(\Delta_k);$$
--   3. after a shrink iteration, $\operatorname{vol}(\Delta_{k+1})=\sigma^n\operatorname{vol}(\Delta_k)$.
--
--   In particular a reflection with $\rho=1$ preserves volume, which the proof of Theorem 5.2 uses.
--
--   **Formalization Note** $\operatorname{vol}(\Delta)=|\det M|/n!$ with $M$ the edge matrix (2.10). The type of iteration $k$ is `tau ρ χ γ (move f ρ χ γ (Δ k))`, i.e. $\rho$, $\rho\chi$, $\rho\gamma$ or $-\gamma$; note that an expansion attempt whose expansion point is rejected accepts $x_r$ and has type $\rho$.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), p. 120, Lemma 3.1

import Mathlib
import Definitions.Def_NelderMeadLD_Dim2_Algorithm
open Filter Topology

namespace NelderMeadLD.Dim2

theorem lemma_3_1 {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ)
    (Δ : ℕ → Fin (n + 1) → E n) (hrun : IsNMRun f ρ χ γ σ Δ) (hnd : Nondegenerate (Δ 0)) :
    (∀ k, Nondegenerate (Δ k)) ∧
    (∀ k, ¬ IsShrinkAt f ρ χ γ Δ k →
      vol (Δ (k + 1)) = |tau ρ χ γ (move f ρ χ γ (Δ k))| * vol (Δ k)) ∧
    (∀ k, IsShrinkAt f ρ χ γ Δ k → vol (Δ (k + 1)) = σ ^ n * vol (Δ k)) := by sorry

end NelderMeadLD.Dim2
