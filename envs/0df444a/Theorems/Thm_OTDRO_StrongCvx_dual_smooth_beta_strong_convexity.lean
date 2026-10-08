-- Prove2me | Theorems.Thm_OTDRO_StrongCvx_dual_smooth_beta_strong_convexity
-- name    : OTDRO.StrongCvx.dual_smooth_beta_strong_convexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:12:37.092968+00:00
-- url     : https://prove2.me/theorems/ed58f1b3-8190-4a5d-a7cc-5f7c55090994
-- title:
--   Theorem 3, p. 11 — bounded Hessian and strong convexity in β
-- statement:
--   Under Assumptions 1–4, let $\underline L,\overline L$ satisfy Lemma 6, assume the compact decision set has positive radius $R_\beta>0$, and use the constants $\delta_0$ and $\kappa_0=\underline L/(2\rho_{\max})$ from pp. 36–37. For every $0<\delta<\delta_0$, the dual objective is finite and twice differentiable on the nonzero part of $\mathbb V$, its Hessian is uniformly bounded there, and for each $(\beta,\lambda)$ in that region and $v\in\mathbb R^d$,
--
--   $$\nabla^2_{\beta\beta}f_\delta(\beta,\lambda)[v,v]\ge\sqrt\delta\,\kappa_0\lambda^{-1}\|v\|^2.$$
--
--   The theorem supplies curvature in decision directions and regularity of the joint objective before Theorem 4 adds curvature in all directions.
--
--   **Formalization Note** Finiteness on a neighborhood, first-order differentiability nearby, and differentiability of the derivative are explicit so Lean's total derivative is a genuine Hessian. The point $\beta=0$ is excluded because the printed differentiability claim fails there in general. Positive $R_\beta$ makes the proof's explicit $\delta_0$ meaningful: nonempty compact $B=\{0\}$ is otherwise allowed by Assumptions 1–4 and would make that formula zero.
-- source:
--   Blanchet, Murthy & Zhang, arXiv:1810.02403v3, Theorem 3, p. 11; proof pp. 36–37

import Mathlib
import Definitions.Def_OTDRO_StrongCvx_RealDual

namespace OTDRO.StrongCvx

open MeasureTheory Filter
open scoped Topology

/-- Theorem 3, p. 11, with δ₀ from p. 36 and κ₀ = L̲/(2ρmax)
from p. 37. Positive `Rbeta B` makes the explicit δ₀ positive. The point β=0
is excluded because differentiability there fails in general. -/
theorem dual_smooth_beta_strong_convexity {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (hB4 : Assumption4 B) (hBne : B.Nonempty)
    (hR : 0 < Rbeta B)
    (M : ℝ) (h3 : Assumption3 P0 ℓ B M)
    (Llow Lbar : ℝ) (hL : DerivSqBounds P0 ℓ B Llow Lbar) :
    0 < delta0 ρmin ρmax Llow (Rbeta B) M ∧
    0 < Llow / (2 * ρmax) ∧
    ∀ δ : ℝ, 0 < δ → δ < delta0 ρmin ρmax Llow (Rbeta B) M →
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ θ ∈ regionV B δ M (Rbeta B) ρmin ρmax Llow Lbar,
        θ.1 ≠ 0 →
        (∀ᶠ θ' in 𝓝 θ, OTDRO.Dual.fDelta P0 ℓ A δ θ'.1 θ'.2 ≠ ⊤ ∧
          OTDRO.Dual.fDelta P0 ℓ A δ θ'.1 θ'.2 ≠ ⊥) ∧
        (∀ᶠ θ' in 𝓝 θ, DifferentiableAt ℝ (dualReal P0 ℓ A δ) θ') ∧
        DifferentiableAt ℝ (fderiv ℝ (dualReal P0 ℓ A δ)) θ ∧
        ‖fderiv ℝ (fderiv ℝ (dualReal P0 ℓ A δ)) θ‖ ≤ C ∧
        ∀ v : EuclideanSpace ℝ (Fin d),
          Real.sqrt δ * (Llow / (2 * ρmax)) / θ.2 * ‖v‖ ^ 2 ≤
            fderiv ℝ (fderiv ℝ (dualReal P0 ℓ A δ)) θ (v, 0) (v, 0) := by sorry

end OTDRO.StrongCvx
