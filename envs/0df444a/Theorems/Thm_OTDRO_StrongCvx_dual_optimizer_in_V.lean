-- Prove2me | Theorems.Thm_OTDRO_StrongCvx_dual_optimizer_in_V
-- name    : OTDRO.StrongCvx.dual_optimizer_in_V
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:11:23.312398+00:00
-- url     : https://prove2.me/theorems/6256a34c-4b7f-45ca-9934-3cbb34b59a7a
-- title:
--   Proposition 1, p. 11 — every dual minimizer lies in V
-- statement:
--   Under Assumptions 1–4, let $\underline L,\overline L$ be any positive pair satisfying Lemma 6's uniform squared-derivative bounds. For any $\beta\in B$ and any minimizer $\lambda_*(\beta)\ge0$ of $f_\delta(\beta,\cdot)$,
--
--   $$(\beta,\lambda_*(\beta))\in\mathbb V=\{(b,\lambda):b\in B,\lambda\ge0,K_1\|b\|\le\lambda\le K_2\|b\|\},$$
--
--   where $K_1$ and $K_2$ have the explicit values of (28). Thus the region used by the Hessian theorems contains the dual optimizers.
--
--   **Formalization Note** The pair $\underline L,\overline L$ is passed with its Lemma 6 property; the proposition holds for any admissible pair. The nonnegative minimizer membership is explicit.
-- source:
--   Blanchet, Murthy & Zhang, arXiv:1810.02403v3, Proposition 1 and (8), p. 11; (28), p. 34

import Mathlib
import Definitions.Def_OTDRO_StrongCvx_Regions

namespace OTDRO.StrongCvx

open MeasureTheory

/-- Proposition 1, p. 11, with K₁ and K₂ taken from (28), p. 34. -/
theorem dual_optimizer_in_V {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d)))
    (hB : Convex ℝ B) (hB4 : Assumption4 B) (hBne : B.Nonempty)
    (M : ℝ) (h3 : Assumption3 P0 ℓ B M)
    (Llow Lbar : ℝ) (hL : DerivSqBounds P0 ℓ B Llow Lbar)
    (β : EuclideanSpace ℝ (Fin d)) (hβB : β ∈ B)
    (lamStar : ℝ) (hlam : 0 ≤ lamStar)
    (hmin : IsMinOn (fun lam => OTDRO.Dual.fDelta P0 ℓ A δ β lam) (Set.Ici 0) lamStar) :
    (β, lamStar) ∈ regionV B δ M (Rbeta B) ρmin ρmax Llow Lbar := by sorry

end OTDRO.StrongCvx
