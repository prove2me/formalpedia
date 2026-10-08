-- Prove2me | Theorems.Thm_OTDRO_StrongCvx_dual_optimizer_bounds
-- name    : OTDRO.StrongCvx.dual_optimizer_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:10:40.15527+00:00
-- url     : https://prove2.me/theorems/462794aa-b773-4016-a5b4-b7e8f35bf140
-- title:
--   Lemma 7, p. 33 — lower and upper bounds on a dual minimizer
-- statement:
--   Assume the paper's Assumptions 1–3 and $\delta>0$. For $\beta\in B$, let $\lambda_*(\beta)\ge0$ minimize the extended-real dual objective $f_\delta(\beta,\lambda)$ over $\lambda\ge0$. Write $S_\beta=\mathbb E_{P_0}[\ell'(\beta^{\mathsf T}X)^2]$. Then
--
--   $$\frac{\|\beta\|\sqrt{S_\beta}}{2\sqrt{\rho_{\max}}}\le\lambda_*(\beta)\le\frac{\|\beta\|\sqrt{S_\beta}}{\sqrt{\rho_{\min}}}+\frac{\sqrt\delta M\|\beta\|^2}{2\rho_{\min}}.$$
--
--   These are the paper's $\lambda_{\min}(\beta)$ and $\lambda_{\max}(\beta)$; Proposition 1 makes them uniform over a compact decision set.
--
--   **Formalization Note** Membership $\lambda_*\ge0$ is stated separately because Lean's `IsMinOn` predicate alone does not include membership in the minimizing set.
-- source:
--   Blanchet, Murthy & Zhang, arXiv:1810.02403v3, Lemma 7, p. 33; proof pp. 33–34

import Mathlib
import Definitions.Def_OTDRO_StrongCvx_Assumptions

namespace OTDRO.StrongCvx

open MeasureTheory

/-- Lemma 7, p. 33: explicit lower and upper bounds for any nonnegative
dual minimizer. -/
theorem dual_optimizer_bounds {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d)))
    (hB : Convex ℝ B) (M : ℝ) (h3 : Assumption3 P0 ℓ B M)
    (β : EuclideanSpace ℝ (Fin d)) (hβB : β ∈ B)
    (lamStar : ℝ) (hlam : 0 ≤ lamStar)
    (hmin : IsMinOn (fun lam => OTDRO.Dual.fDelta P0 ℓ A δ β lam) (Set.Ici 0) lamStar) :
    (1 / 2) / Real.sqrt ρmax * ‖β‖ *
      Real.sqrt (∫ x, (deriv ℓ (inner ℝ β x)) ^ 2 ∂P0) ≤ lamStar ∧
    lamStar ≤ (1 / Real.sqrt ρmin) * ‖β‖ *
      Real.sqrt (∫ x, (deriv ℓ (inner ℝ β x)) ^ 2 ∂P0) +
      (1 / 2) * Real.sqrt δ * M / ρmin * ‖β‖ ^ 2 := by sorry

end OTDRO.StrongCvx
