-- Prove2me | Theorems.Thm_OTDRO_WorstCase_maximizers_bounded
-- name    : OTDRO.WorstCase.maximizers_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:05:21.252767+00:00
-- url     : https://prove2.me/theorems/a958600e-4496-445f-8f6c-a5677e04bf00
-- title:
--   Lemma 3(a), p. 32 — every g ∈ Γ* satisfies √δ|g|βᵀA(x)⁻¹β ≤ 1 + C₁ε⁻¹(1 + |βᵀx|) once λ ≥ (κ + ε)√δβᵀA(x)⁻¹β
-- statement:
--   Assume Assumptions 1 and 2, $\delta>0$ and $B\subseteq\mathbb R^d$ convex, and let $\kappa$ be the growth exponent of $\ell$. For every $\varepsilon>0$, $x\in\mathbb R^d$, $\beta\in B$ and $\lambda\ge(\kappa+\varepsilon)\sqrt\delta\,\beta^{\mathsf T}A(x)^{-1}\beta$, there is a constant $C_1>0$ such that every maximizer $g\in\Gamma^*(\beta,\lambda;x)$ of $\gamma\mapsto F(\gamma,\beta,\lambda;x)$ satisfies
--   $$\sqrt\delta\,|g|\,\beta^{\mathsf T}A(x)^{-1}\beta\ \le\ 1+C_1\varepsilon^{-1}\bigl(1+|\beta^{\mathsf T}x|\bigr).$$
--
--   The bound shows that the maximizer set is bounded, hence compact, as soon as $\lambda$ exceeds the threshold, and that the worst-case displacement grows at most linearly in $|\beta^{\mathsf T}x|$. It is what makes the extreme points $\inf$ and $\sup$ of $\gamma^2$ over $\Gamma^*$ attained in the proof of Theorem 6(c), and what makes the moments $E[G_\pm^2\beta^{\mathsf T}A(X)^{-1}\beta]$ finite.
--
--   **Formalization Note** The constant $C_1$ is quantified after $\varepsilon$, $x$, $\beta$ and $\lambda$, as in the printed lemma. Only part (a) of Lemma 3 is formalized here; part (b) is in the sibling mission on convexity of the dual objective.
-- source:
--   arXiv:1810.02403v3, Lemma 3(a), p. 32; proof p. 47

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting

open MeasureTheory

namespace OTDRO.WorstCase

/-- **Lemma 3(a)** (arXiv:1810.02403v3, p. 32; proof p. 47), with the constant `C₁` chosen after
`ε`, `x`, `β` and `λ`, as the printed lemma states: if
`λ ≥ (κ + ε)√δ βᵀA(x)⁻¹β`, every `g ∈ Γ*(β, λ; x)` satisfies
`√δ |g| βᵀA(x)⁻¹β ≤ 1 + C₁ ε⁻¹ (1 + |βᵀx|)`. -/
theorem maximizers_bounded {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0] (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax) (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B) :
    ∀ ε : ℝ, 0 < ε → ∀ x : EuclideanSpace ℝ (Fin d), ∀ β ∈ B, ∀ lam : ℝ,
      (OTDRO.Dual.growthKappa ℓ + ε) * Real.sqrt δ * OTDRO.Dual.quadInv A β x ≤ lam →
      ∃ C1 : ℝ, 0 < C1 ∧
        ∀ g ∈ OTDRO.Dual.maximizers ℓ A δ β lam x,
          Real.sqrt δ * |g| * OTDRO.Dual.quadInv A β x ≤ 1 + C1 * ε⁻¹ * (1 + |inner ℝ β x|) := by sorry

end OTDRO.WorstCase
