-- Prove2me | Theorems.Thm_OTDRO_StrongCvx_maximizer_first_order
-- name    : OTDRO.StrongCvx.maximizer_first_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:21.264074+00:00
-- url     : https://prove2.me/theorems/35b5a59a-458e-4926-831e-8b7925e16ff2
-- title:
--   Lemma 5, p. 33 — first-order identity and lower bound for γ
-- statement:
--   Let $\gamma$ maximize $F(\cdot,\beta,\lambda;x)$, with nonzero $\beta\in B$, $\lambda>0$, and a differentiable convex loss $\ell$. Under Assumptions 1–2 and $\delta>0$,
--
--   $$\gamma=\frac{\ell'(\beta^{\mathsf T}x+\gamma\sqrt\delta\,q_A(\beta,x))}{2\lambda},\qquad |\gamma|\ge\frac{|\ell'(\beta^{\mathsf T}x)|}{2\lambda}.$$
--
--   This is the pointwise link between the maximizing scalar and the loss derivative used in the multiplier and curvature bounds.
--
--   **Formalization Note** Differentiability, $\beta\ne0$, and $\lambda>0$ are explicit corrections to the printed statement; at $\beta=0$ the maximizing scalar need not be unique, and the displayed quotient is undefined at $\lambda=0$.
-- source:
--   Blanchet, Murthy & Zhang, arXiv:1810.02403v3, Lemma 5 and (27), p. 33

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting

namespace OTDRO.StrongCvx

open MeasureTheory

/-- Lemma 5, p. 33, including (27). The paper's differentiability, nonzero β,
and λ > 0 requirements are made explicit. -/
theorem maximizer_first_order {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d)))
    (hB : Convex ℝ B) (β : EuclideanSpace ℝ (Fin d))
    (hβB : β ∈ B) (hβ : β ≠ 0) (x : EuclideanSpace ℝ (Fin d))
    (lam : ℝ) (hlam : 0 < lam) (hℓ : Differentiable ℝ ℓ)
    (hne : (OTDRO.Dual.maximizers ℓ A δ β lam x).Nonempty) :
    ∀ γ ∈ OTDRO.Dual.maximizers ℓ A δ β lam x,
      γ = deriv ℓ (inner ℝ β x + Real.sqrt δ * γ * OTDRO.Dual.quadInv A β x) / (2 * lam) ∧
      |deriv ℓ (inner ℝ β x)| / (2 * lam) ≤ |γ| := by sorry

end OTDRO.StrongCvx
