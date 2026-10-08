-- Prove2me | Theorems.Thm_OTDRO_Statics_prop9_a
-- name    : OTDRO.Statics.prop9_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:25.943514+00:00
-- url     : https://prove2.me/theorems/8185ff79-8c8a-435f-970d-3e38e3107ec0
-- title:
--   Proposition 9(a) — the optimizer region lies above the smoothness threshold
-- statement:
--   Under Assumptions 1–4 and $0<\delta<\delta_0$, the narrow region is contained in the wider one. For every nonzero $\beta\in B$, each $(\beta,\lambda)\in\mathbb W$ lies strictly above the threshold $\lambda'_{\rm thr}(\beta)$:
--
--   $$\mathbb V\subseteq\mathbb W,\qquad \lambda>\lambda'_{\rm thr}(\beta).$$
--
--   Moreover, for $P_0$-almost every $x$, every $(\beta,\lambda)$ with $\beta\in B$ and $\lambda>\lambda'_{\rm thr}(\beta)$ belongs to $\mathcal U(x)$, the positive-curvature maximizer region.
--
--   This places dual optimizers in the regime where the scalar maximizer is unique.
--
--   **Formalization Note** The $\mathbb W$-to-threshold assertion excludes $\beta=0$: at $(0,0)\in\mathbb W$ the printed strict inequality fails. The threshold-to-$\mathcal U(x)$ inclusion includes $\beta=0$ when $\lambda>0$. The bounds $\underline L,\overline L$ are the admissible pair supplied by Lemma 6.
-- source:
--   arXiv:1810.02403v3, Proposition 9(a), p. 37

import Mathlib
import Definitions.Def_OTDRO_Statics_Regions

namespace OTDRO.Statics

open MeasureTheory

/-- Proposition 9(a), p. 37, restricted to nonzero β as required by its threshold claim. -/
theorem prop9_a {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
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
    (hsmall : δ < OTDRO.StrongCvx.delta0 ρmin ρmax Llow (Rβ B) M) :
    OTDRO.StrongCvx.regionV B δ M (Rβ B) ρmin ρmax Llow Lbar ⊆
      OTDRO.StrongCvx.regionW B δ M (Rβ B) ρmin ρmax Llow Lbar ∧
    (∀ β ∈ B, β ≠ 0 → ∀ lam : ℝ,
      (β, lam) ∈ OTDRO.StrongCvx.regionW B δ M (Rβ B) ρmin ρmax Llow Lbar →
      OTDRO.Dual.lamThr' P0 A M δ β < lam) ∧
    ∀ᵐ x ∂P0,
      {θ : EuclideanSpace ℝ (Fin d) × ℝ |
        θ.1 ∈ B ∧ OTDRO.Dual.lamThr' P0 A M δ θ.1 < θ.2} ⊆
        regionU P0 ℓ A δ B x := by sorry

end OTDRO.Statics
