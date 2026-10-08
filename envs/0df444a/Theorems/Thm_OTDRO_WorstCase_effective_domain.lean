-- Prove2me | Theorems.Thm_OTDRO_WorstCase_effective_domain
-- name    : OTDRO.WorstCase.effective_domain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:05:26.989968+00:00
-- url     : https://prove2.me/theorems/55edcb58-e0b9-4be3-908f-f699e9426bc4
-- title:
--   Lemma 1, p. 16 — Γ* ≠ ∅ and ℓ_rob < ∞ above κ√δβᵀA(x)⁻¹β, ℓ_rob = ∞ below; 𝕌₁ ⊆ 𝕌 ⊆ 𝕌₂
-- statement:
--   Assume Assumptions 1 and 2, let $\delta>0$ and let $B\subseteq\mathbb R^d$ be convex. Write $\kappa$ for the growth exponent of $\ell$, $\Gamma^*(\beta,\lambda;x)$ for the set of maximizers of $\gamma\mapsto F(\gamma,\beta,\lambda;x)$, $\ell_{\rm rob}=\sup_\gamma F$ and $f_\delta(\beta,\lambda)=E_{P_0}[\ell_{\rm rob}(\beta,\lambda;X)]$. Then for every $\beta\in B$, $\lambda\ge0$ and $x\in\mathbb R^d$:
--
--   1. if $\lambda>\kappa\sqrt\delta\,\beta^{\mathsf T}A(x)^{-1}\beta$, then $\Gamma^*(\beta,\lambda;x)\neq\emptyset$ and $\ell_{\rm rob}(\beta,\lambda;x)<\infty$;
--   2. if $\lambda<\kappa\sqrt\delta\,\beta^{\mathsf T}A(x)^{-1}\beta$, then $\Gamma^*(\beta,\lambda;x)=\emptyset$ and $\ell_{\rm rob}(\beta,\lambda;x)=\infty$.
--
--   Consequently, with $\mathbb U=\{(\beta,\lambda)\in B\times\mathbb R_+: f_\delta(\beta,\lambda)<\infty\}$,
--   $$\mathbb U_1=\{\lambda>\lambda_{thr}(\beta)\}\ \subseteq\ \mathbb U\ \subseteq\ \mathbb U_2=\{\lambda\ge\lambda_{thr}(\beta)\}.$$
--
--   The lemma identifies the effective domain of the dual objective up to its boundary $\lambda=\lambda_{thr}(\beta)$; it is the reason a dual optimizer always satisfies $\lambda_*(\beta)\ge\lambda_{thr}(\beta)$ and the region where the worst case of Theorem 6(c) is analysed.
--
--   **Formalization Note** The page prints the threshold as "$\kappa\sqrt\delta\beta A(x)^{-1}\beta$", a typo for $\beta^{\mathsf T}A(x)^{-1}\beta$. The inclusions are stated pointwise: for $\beta\in B$ and $\lambda\ge0$, $\lambda>\lambda_{thr}(\beta)$ implies $f_\delta(\beta,\lambda)<\infty$, and $f_\delta(\beta,\lambda)<\infty$ implies $\lambda\ge\lambda_{thr}(\beta)$. $\ell_{\rm rob}$ is a supremum of real numbers over $\mathbb R$, so it is never $-\infty$, and "finite" is written $\ell_{\rm rob}\ne+\infty$. The same statement is drafted in the sibling mission on convexity of the dual objective.
-- source:
--   arXiv:1810.02403v3, Lemma 1, p. 16; (11), p. 15; proof p. 47

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting

open MeasureTheory

namespace OTDRO.WorstCase

/-- **Lemma 1** (arXiv:1810.02403v3, p. 16; proof p. 47). (a) If `λ > κ√δ βᵀA(x)⁻¹β` then
`Γ*(β, λ; x)` is nonempty and `ℓ_rob(β, λ; x)` is finite; (b) if `λ < κ√δ βᵀA(x)⁻¹β` then
`Γ*(β, λ; x) = ∅` and `ℓ_rob(β, λ; x) = ∞`; consequently `𝕌₁ ⊆ 𝕌 ⊆ 𝕌₂`, where
`𝕌 = {(β, λ) ∈ B × ℝ₊ : f_δ(β, λ) < ∞}`, `𝕌₁` (resp. `𝕌₂`) is `λ > λ_thr(β)` (resp. `≥`). -/
theorem effective_domain {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0] (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax) (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B) :
    (∀ β ∈ B, ∀ lam : ℝ, 0 ≤ lam → ∀ x : EuclideanSpace ℝ (Fin d),
      (OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * OTDRO.Dual.quadInv A β x < lam →
        (OTDRO.Dual.maximizers ℓ A δ β lam x).Nonempty ∧ OTDRO.Dual.ellRob ℓ A δ β lam x ≠ ⊤) ∧
      (lam < OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * OTDRO.Dual.quadInv A β x →
        OTDRO.Dual.maximizers ℓ A δ β lam x = ∅ ∧ OTDRO.Dual.ellRob ℓ A δ β lam x = ⊤)) ∧
    (∀ β ∈ B, ∀ lam : ℝ, 0 ≤ lam → OTDRO.Dual.lamThr P0 ℓ A δ β < lam → OTDRO.Dual.fDelta P0 ℓ A δ β lam < ⊤) ∧
    (∀ β ∈ B, ∀ lam : ℝ, 0 ≤ lam → OTDRO.Dual.fDelta P0 ℓ A δ β lam < ⊤ → OTDRO.Dual.lamThr P0 ℓ A δ β ≤ lam) := by sorry

end OTDRO.WorstCase
