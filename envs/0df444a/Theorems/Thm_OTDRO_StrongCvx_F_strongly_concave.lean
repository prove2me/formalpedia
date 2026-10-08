-- Prove2me | Theorems.Thm_OTDRO_StrongCvx_F_strongly_concave
-- name    : OTDRO.StrongCvx.F_strongly_concave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:12:07.739809+00:00
-- url     : https://prove2.me/theorems/296e5d39-5349-4954-9ba2-34feeae0b919
-- title:
--   Lemma 8, p. 36 — strong concavity and unique maximizer
-- statement:
--   Assume Assumptions 1–3 and $\delta>0$. For $P_0$-almost every $x$ (one null set for all parameters), every nonzero $\beta\in B$ and every $\lambda>\lambda'_{\rm thr}(\beta)$, the function $\gamma\mapsto F(\gamma,\beta,\lambda;x)$ is strongly concave and has a unique maximizer. Its parameter pair belongs to the positive-curvature section $U(x)$:
--
--   $$\Gamma^*(\beta,\lambda;x)=\{g(\beta,\lambda;x)\},\qquad (\beta,\lambda)\in U(x).$$
--
--   The unique scalar is the one used to express the pointwise Hessian and the bounds in Proposition 9.
--
--   **Formalization Note** Strong concavity is the standard interpolation inequality with a positive modulus. The printed statement includes $\beta=0$, where $F$ is constant in $\gamma$ and the conclusion fails; the nonzero condition is explicit.
-- source:
--   Blanchet, Murthy & Zhang, arXiv:1810.02403v3, Lemma 8, p. 36; proof p. 55

import Mathlib
import Definitions.Def_OTDRO_StrongCvx_Kernel

namespace OTDRO.StrongCvx

open MeasureTheory

/-- Lemma 8, p. 36. Strong concavity is written as its interpolation inequality,
including attainment, uniqueness, and membership in U(x). The P₀-null set is
uniform in (β, λ), as in the printed inclusion {(β, λ) : …} ⊆ U(x) for P₀-a.e. x.
β=0 is excluded because then F is constant in γ. -/
theorem F_strongly_concave {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d)))
    (hB : Convex ℝ B) (M : ℝ) (h3 : Assumption3 P0 ℓ B M) :
    ∀ᵐ x ∂P0, ∀ β ∈ B, β ≠ 0 → ∀ lam : ℝ, OTDRO.Dual.lamThr' P0 A M δ β < lam →
      ∃ m : ℝ, 0 < m ∧
        (∀ γ₁ γ₂ t : ℝ, 0 ≤ t → t ≤ 1 →
          t * OTDRO.Dual.Fobj ℓ A δ γ₁ β lam x + (1 - t) * OTDRO.Dual.Fobj ℓ A δ γ₂ β lam x +
              m / 2 * t * (1 - t) * (γ₁ - γ₂) ^ 2 ≤
            OTDRO.Dual.Fobj ℓ A δ (t * γ₁ + (1 - t) * γ₂) β lam x) ∧
        (∃ γ : ℝ, OTDRO.Dual.maximizers ℓ A δ β lam x = {γ}) ∧
        (β, lam) ∈ UAt B ℓ A δ x := by sorry

end OTDRO.StrongCvx
