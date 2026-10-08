-- Prove2me | Theorems.Thm_OTDRO_StrongCvx_dual_joint_strong_convexity
-- name    : OTDRO.StrongCvx.dual_joint_strong_convexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:12:12.001977+00:00
-- url     : https://prove2.me/theorems/ad7c3d30-a05a-4832-b2f3-73e28afccd6d
-- title:
--   Theorem 4, p. 11 — joint √δ-strong convexity near dual optimizers
-- statement:
--   Assume the state-dependent Mahalanobis model, Assumptions 1–5, a nonempty compact convex decision set $B$, and any positive constants $\underline L,\overline L$ satisfying Lemma 6. There exist $\delta_1\in(0,\delta_0)$ and $\kappa_1>0$ such that, for every $0<\delta<\delta_1$ and $(\beta,\lambda)\in\mathbb V_\delta$,
--
--   $$\nabla^2 f_\delta(\beta,\lambda)\succeq\sqrt\delta\,\kappa_1 I_{d+1}.$$
--
--   Here $\mathbb V_\delta$ contains every dual minimizer by Proposition 1. The same $\kappa_1$ applies to all sufficiently small radii, which is the joint strong-convexity conclusion of the paper.
--
--   **Formalization Note** The Hessian is the Fréchet second derivative of the real representative of the extended-real $f_\delta$ on a finite neighborhood. Its quadratic form is evaluated as $\|v_\beta\|^2+v_\lambda^2$. Assumption 5's strict score condition itself excludes $\beta=0$ from $B$; no extra nonzero guard is needed. The pair $\underline L,\overline L$ is any pair with Lemma 6's property, and nonemptiness of $B$ is explicit.
-- source:
--   Blanchet, Murthy & Zhang, arXiv:1810.02403v3, Theorem 4, p. 11; proof pp. 37–39

import Mathlib
import Definitions.Def_OTDRO_StrongCvx_RealDual

namespace OTDRO.StrongCvx

open MeasureTheory Filter
open scoped Topology

/-- Theorem 4, p. 11: a δ-uniform positive joint Hessian modulus on V.
Assumption 5 already rules out β=0 for β∈B. -/
theorem dual_joint_strong_convexity {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (hB4 : Assumption4 B) (hBne : B.Nonempty)
    (M : ℝ) (h3 : Assumption3 P0 ℓ B M)
    (h5 : Assumption5 P0 ℓ B)
    (Llow Lbar : ℝ) (hL : DerivSqBounds P0 ℓ B Llow Lbar) :
    ∃ δ1 κ1 : ℝ,
      0 < δ1 ∧ δ1 < delta0 ρmin ρmax Llow (Rbeta B) M ∧ 0 < κ1 ∧
      ∀ δ : ℝ, 0 < δ → δ < δ1 →
        ∀ θ ∈ regionV B δ M (Rbeta B) ρmin ρmax Llow Lbar,
          (∀ᶠ θ' in 𝓝 θ, OTDRO.Dual.fDelta P0 ℓ A δ θ'.1 θ'.2 ≠ ⊤ ∧
          OTDRO.Dual.fDelta P0 ℓ A δ θ'.1 θ'.2 ≠ ⊥) ∧
          (∀ᶠ θ' in 𝓝 θ, DifferentiableAt ℝ (dualReal P0 ℓ A δ) θ') ∧
          DifferentiableAt ℝ (fderiv ℝ (dualReal P0 ℓ A δ)) θ ∧
          ∀ v : EuclideanSpace ℝ (Fin d) × ℝ,
            Real.sqrt δ * κ1 * (‖v.1‖ ^ 2 + v.2 ^ 2) ≤
              fderiv ℝ (fderiv ℝ (dualReal P0 ℓ A δ)) θ v v := by sorry

end OTDRO.StrongCvx
