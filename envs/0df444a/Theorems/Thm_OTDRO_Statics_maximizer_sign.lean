-- Prove2me | Theorems.Thm_OTDRO_Statics_maximizer_sign
-- name    : OTDRO.Statics.maximizer_sign
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:29.196979+00:00
-- url     : https://prove2.me/theorems/9fdf5a4d-57bf-4cd2-89e5-680a3211c82f
-- title:
--   §5.4 — the displacement coefficient has the sign of the loss derivative
-- statement:
--   Under Assumptions 1–4 with $0<\delta<\delta_0$, fix nonzero $\beta\in B$, a nonnegative dual optimizer $\lambda$, and the almost-sure unique maximizer $G(x)$ of the scalar objective. Then, for $P_0$-almost every $x$,
--
--   There is a number $\eta$ between $\beta^\top x$ and $\beta^\top X^*$, where $X^*=x+\sqrt\delta G(x)A(x)^{-1}\beta$, such that
--
--   $$G(x)=\frac{\ell'(\beta^\top x)}{2\lambda-\sqrt\delta\,\beta^\top A(x)^{-1}\beta\,\ell''(\eta)},\qquad
--   2\lambda-\sqrt\delta\,\beta^\top A(x)^{-1}\beta\,\ell''(\eta)\ge\varphi_{\min}\|\beta\|>0.$$
--
--   In particular, $\operatorname{sgn}G(x)=\operatorname{sgn}\ell'(\beta^\top x)$.
--
--   Thus a positive score moves the observation forward along $A(x)^{-1}\beta$, a negative score moves it backward, and a zero score produces no displacement. This supplies the sign cases of Theorem 7.
--
--   **Formalization Note** $G$ is identified by its almost-sure singleton maximizer property; it is not an arbitrary scalar field.
-- source:
--   arXiv:1810.02403v3, §5.4, proof of Theorem 7, p. 41, final paragraph

import Mathlib
import Definitions.Def_OTDRO_Statics_Regions
import Definitions.Def_OTDRO_Statics_Transport

namespace OTDRO.Statics

open MeasureTheory

/-- The sign assertion in §5.4, proof of Theorem 7, p. 41. -/
theorem maximizer_sign {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ)
    (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (hB4 : OTDRO.StrongCvx.Assumption4 B) (hBne : B.Nonempty)
    (M : ℝ) (h3 : OTDRO.StrongCvx.Assumption3 P0 ℓ B M)
    (Llow Lbar : ℝ)
    (hL : 0 < Llow ∧ ∀ β ∈ B,
      Llow ≤ ∫ x, (deriv ℓ (inner ℝ β x)) ^ 2 ∂P0 ∧
      ∫ x, (deriv ℓ (inner ℝ β x)) ^ 2 ∂P0 ≤ Lbar)
    (hsmall : δ < OTDRO.StrongCvx.delta0 ρmin ρmax Llow (Rβ B) M)
    (β : EuclideanSpace ℝ (Fin d)) (hβB : β ∈ B) (hβ : β ≠ 0)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hmin : IsMinOn (fun l => OTDRO.Dual.fDelta P0 ℓ A δ β l) (Set.Ici 0) lam)
    (G : EuclideanSpace ℝ (Fin d) → ℝ)
    (hG : ∀ᵐ x ∂P0, OTDRO.Dual.maximizers ℓ A δ β lam x = {G x}) :
    ∀ᵐ x ∂P0,
      (∃ η : ℝ,
        min (inner ℝ β x) (inner ℝ β (shiftMap A δ β G x)) ≤ η ∧
        η ≤ max (inner ℝ β x) (inner ℝ β (shiftMap A δ β G x)) ∧
        G x = deriv ℓ (inner ℝ β x) /
          (2 * lam - Real.sqrt δ * OTDRO.Dual.quadInv A β x * deriv (deriv ℓ) η) ∧
        OTDRO.StrongCvx.phiMin δ Llow ρmax (Rβ B) M ρmin * ‖β‖ ≤
          2 * lam - Real.sqrt δ * OTDRO.Dual.quadInv A β x * deriv (deriv ℓ) η ∧
        0 < OTDRO.StrongCvx.phiMin δ Llow ρmax (Rβ B) M ρmin * ‖β‖) ∧
      (0 < deriv ℓ (inner ℝ β x) → 0 < G x) ∧
      (deriv ℓ (inner ℝ β x) < 0 → G x < 0) ∧
      (deriv ℓ (inner ℝ β x) = 0 → G x = 0) := by sorry

end OTDRO.Statics
