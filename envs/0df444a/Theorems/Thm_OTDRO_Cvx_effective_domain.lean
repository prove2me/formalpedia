-- Prove2me | Theorems.Thm_OTDRO_Cvx_effective_domain
-- name    : OTDRO.Cvx.effective_domain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:19.915987+00:00
-- url     : https://prove2.me/theorems/04851d15-7aba-410d-9913-8f15eed87dd1
-- title:
--   Lemma 1, p. 16 — Γ* ≠ ∅ and ℓ_rob finite above κ√δ βᵀA(x)⁻¹β, ℓ_rob = ∞ below; U₁ ⊆ U ⊆ U₂
-- statement:
--   Assume Assumptions 1 and 2, let $\delta > 0$ and let $B \subseteq \mathbb{R}^d$ be convex; $\kappa$ is the growth exponent of $\ell$. Then for every $\beta \in B$, $\lambda \ge 0$ and $x \in \mathbb{R}^d$:
--
--   1. if $\lambda > \kappa\sqrt{\delta}\,\beta^{\mathsf T}A(x)^{-1}\beta$, then the maximizer set $\Gamma^*(\beta, \lambda; x)$ is nonempty and $\ell_{rob}(\beta, \lambda; x)$ is a finite real number;
--   2. if $\lambda < \kappa\sqrt{\delta}\,\beta^{\mathsf T}A(x)^{-1}\beta$, then $\Gamma^*(\beta, \lambda; x)$ is empty and $\ell_{rob}(\beta, \lambda; x) = +\infty$.
--
--   Consequently the effective domain $\mathbb{U}$ of $f_\delta$ satisfies
--   $$\mathbb{U}_1 \subseteq \mathbb{U} \subseteq \mathbb{U}_2,$$
--   where $\mathbb{U}_1$, $\mathbb{U}_2$ are the sets of $(\beta, \lambda) \in B \times \mathbb{R}_+$ with $\lambda > \lambda_{thr}(\beta)$, respectively $\lambda \ge \lambda_{thr}(\beta)$.
--
--   The lemma identifies, up to the boundary $\lambda = \lambda_{thr}(\beta)$, where the dual objective is finite.
--
--   **Formalization Note** The page writes "$\beta A(x)^{-1}\beta$" in (a) and (b), a typo for $\beta^{\mathsf T}A(x)^{-1}\beta$; the Lean uses the quadratic form. "Finite" is written as $\ell_{rob} = r$ for some real $r$. The same lemma is also drafted in mission 4 of this series, because draft items of parallel missions cannot import each other.
-- source:
--   arXiv:1810.02403v3, Lemma 1, p. 16 (proof in Appendix A, pp. 47–48)

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting
import Definitions.Def_OTDRO_Cvx_Domain

namespace OTDRO.Cvx

open MeasureTheory

/-- **Lemma 1**, p. 16: under Assumptions 1–2, for every `β ∈ B`, `λ ≥ 0` and `x ∈ ℝ^d`,
(a) if `λ > κ√δ βᵀA(x)⁻¹β` then `Γ*(β, λ; x)` is nonempty and `ℓ_rob(β, λ; x)` is finite;
(b) if `λ < κ√δ βᵀA(x)⁻¹β` then `Γ*(β, λ; x)` is empty and `ℓ_rob(β, λ; x) = +∞`;
consequently `U₁ ⊆ U ⊆ U₂`. -/
theorem effective_domain {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (ρmin ρmax : ℝ)
    (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (h2 : OTDRO.Dual.Assumption2 P0 ℓ) :
    (∀ β ∈ B, ∀ lam : ℝ, 0 ≤ lam → ∀ x : EuclideanSpace ℝ (Fin d),
      (OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * OTDRO.Dual.quadInv A β x < lam →
        (OTDRO.Dual.maximizers ℓ A δ β lam x).Nonempty ∧ ∃ r : ℝ, OTDRO.Dual.ellRob ℓ A δ β lam x = (r : EReal)) ∧
      (lam < OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * OTDRO.Dual.quadInv A β x →
        OTDRO.Dual.maximizers ℓ A δ β lam x = ∅ ∧ OTDRO.Dual.ellRob ℓ A δ β lam x = ⊤)) ∧
    domU1 P0 ℓ A δ B ⊆ effDomain P0 ℓ A δ B ∧ effDomain P0 ℓ A δ B ⊆ domU2 P0 ℓ A δ B := by sorry

end OTDRO.Cvx
