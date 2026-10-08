-- Prove2me | Theorems.Thm_OTDRO_Cvx_lemma_3
-- name    : OTDRO.Cvx.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:13.939621+00:00
-- url     : https://prove2.me/theorems/bf3c0e05-cd0b-4ab8-b056-5242cb3bb4c4
-- title:
--   Lemma 3, p. 32 — for λ ≥ (κ+ε)√δ βᵀA(x)⁻¹β, maximizers are bounded and ℓ_rob ≤ λ√δ + C₂(1+ε+ε⁻¹)(1+|βᵀx|)²
-- statement:
--   Assume Assumptions 1 and 2, let $\delta > 0$ and let $B \subseteq \mathbb{R}^d$ be convex. Write $\kappa$ for the growth exponent of $\ell$, $q_\beta(x) = \beta^{\mathsf T}A(x)^{-1}\beta$, and $\Gamma^*(\beta, \lambda; x)$ for the set of maximizers of $\gamma \mapsto F(\gamma, \beta, \lambda; x)$.
--
--   Fix $\varepsilon > 0$. Then there exist positive constants $C_1, C_2$ such that for every $x \in \mathbb{R}^d$, every $\beta \in B$ and every $\lambda \ge (\kappa + \varepsilon)\sqrt{\delta}\, q_\beta(x)$,
--
--   1. every $g \in \Gamma^*(\beta, \lambda; x)$ satisfies
--   $$\sqrt{\delta}\,|g|\, \beta^{\mathsf T}A(x)^{-1}\beta \le 1 + C_1 \varepsilon^{-1}(1 + |\beta^{\mathsf T}x|);$$
--   2. the robust loss satisfies
--   $$\ell_{rob}(\beta, \lambda; x) \le \lambda\sqrt{\delta} + C_2(1 + \varepsilon + \varepsilon^{-1})(1 + |\beta^{\mathsf T}x|)^2.$$
--
--   The bound (2) is what makes $f_\delta$ finite for $\lambda$ above the threshold, and (1) confines the maximizers to a bounded interval.
--
--   **Formalization Note** The paper's sentence reads "Consider any $\varepsilon > 0$, $x$ and $\beta$. If $\lambda \ge \dots$, then there exist positive constants $C_1, C_2$". The constants are stated here as depending only on $\varepsilon$ (and the fixed data $\ell$, $A$, $\delta$, $B$, $P_0$), not on $x$, $\beta$, $\lambda$: that is how the proof in Appendix A produces them (from $C_\varepsilon$, $\kappa$, $\ell(0)$ and a subgradient of $\ell$ at $0$), and the proofs of Lemma 1 (p. 48) and Theorem 2 (p. 33) integrate bound (2) against $P_0$, which needs a $C_2$ independent of $x$. With constants allowed to depend on $x$ the bounds would only say that $\Gamma^*$ is bounded and $\ell_{rob}$ is finite. The inequality in (2) is between extended reals.
-- source:
--   arXiv:1810.02403v3, Lemma 3, p. 32 (proof in Appendix A, p. 47)

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting

namespace OTDRO.Cvx

open MeasureTheory

/-- **Lemma 3**, p. 32: for any `ε > 0` there exist positive constants `C₁, C₂` such that for
every `x ∈ ℝ^d`, `β ∈ B` and `λ ≥ (κ + ε)√δ βᵀA(x)⁻¹β`,
(a) every maximizer `g ∈ Γ*(β, λ; x)` has `√δ|g| βᵀA(x)⁻¹β ≤ 1 + C₁ε⁻¹(1 + |βᵀx|)`, and
(b) `ℓ_rob(β, λ; x) ≤ λ√δ + C₂(1 + ε + ε⁻¹)(1 + |βᵀx|)²`.
The constants do not depend on `x`, `β`, `λ`: so the proof (p. 47) produces them, and so the
proofs of Lemma 1 (p. 48) and Theorem 2 (p. 33) integrate bound (b) against `P₀`. -/
theorem lemma_3 {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (ρmin ρmax : ℝ)
    (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (h2 : OTDRO.Dual.Assumption2 P0 ℓ) :
    ∀ ε : ℝ, 0 < ε → ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ x : EuclideanSpace ℝ (Fin d), ∀ β ∈ B, ∀ lam : ℝ,
        (OTDRO.Dual.growthKappa ℓ + ε) * Real.sqrt δ * OTDRO.Dual.quadInv A β x ≤ lam →
        (∀ g ∈ OTDRO.Dual.maximizers ℓ A δ β lam x,
          Real.sqrt δ * |g| * OTDRO.Dual.quadInv A β x ≤ 1 + C₁ * ε⁻¹ * (1 + |inner ℝ β x|)) ∧
        OTDRO.Dual.ellRob ℓ A δ β lam x ≤
          ((lam * Real.sqrt δ + C₂ * (1 + ε + ε⁻¹) * (1 + |inner ℝ β x|) ^ 2 : ℝ) : EReal) := by sorry

end OTDRO.Cvx
