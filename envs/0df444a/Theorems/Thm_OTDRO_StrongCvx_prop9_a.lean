-- Prove2me | Theorems.Thm_OTDRO_StrongCvx_prop9_a
-- name    : OTDRO.StrongCvx.prop9_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:12:20.204979+00:00
-- url     : https://prove2.me/theorems/8988f399-999a-409b-bb1d-7c8ce763831f
-- title:
--   Proposition 9(a), p. 37 — V lies in W and the curvature domain
-- statement:
--   Under Assumptions 1–4 and $0<\delta<\delta_0$, the parameter regions satisfy $\mathbb V\subseteq\mathbb W$. For $P_0$-almost every $x$, every $(\beta,\lambda)\in\mathbb W$ with $\beta\ne0$ also satisfies
--
--   $$\lambda>\lambda'_{\rm thr}(\beta),\qquad (\beta,\lambda)\in U(x).$$
--
--   This locates the optimizer region inside the domain where the scalar maximizer is unique and the curvature margin is positive.
--
--   **Formalization Note** At $\beta=0$ the printed second inclusion can fail at $(0,0)\in\mathbb W$, so it is stated on the nonzero part of $\mathbb W$. The almost-everywhere claim is uniform over the parameters, as printed.
-- source:
--   Blanchet, Murthy & Zhang, arXiv:1810.02403v3, Proposition 9(a), p. 37; proof p. 55

import Mathlib
import Definitions.Def_OTDRO_StrongCvx_Kernel

namespace OTDRO.StrongCvx

open MeasureTheory

/-- Proposition 9(a), p. 37. The point β=0 is excluded in the second
inclusion; the printed inclusion fails there when 0∈B. -/
theorem prop9_a {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d)))
    (hB : Convex ℝ B) (hB4 : Assumption4 B) (hBne : B.Nonempty)
    (M : ℝ) (h3 : Assumption3 P0 ℓ B M)
    (Llow Lbar : ℝ) (hL : DerivSqBounds P0 ℓ B Llow Lbar)
    (hδ0 : δ < delta0 ρmin ρmax Llow (Rbeta B) M) :
    regionV B δ M (Rbeta B) ρmin ρmax Llow Lbar ⊆
        regionW B δ M (Rbeta B) ρmin ρmax Llow Lbar ∧
      ∀ᵐ x ∂P0, ∀ θ ∈ regionW B δ M (Rbeta B) ρmin ρmax Llow Lbar,
        θ.1 ≠ 0 → OTDRO.Dual.lamThr' P0 A M δ θ.1 < θ.2 ∧ θ ∈ UAt B ℓ A δ x := by sorry

end OTDRO.StrongCvx
