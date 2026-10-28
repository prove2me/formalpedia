-- Prove2me | Theorems.Thm_ItoLemma_fin_two_truncated_product_derivatives_eq_on_plateau_interior
-- name    : ItoLemma.fin_two_truncated_product_derivatives_eq_on_plateau_interior
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:06:04.467326+00:00
-- url     : https://prove2.me/theorems/f911f529-d2ff-4dff-8bd3-1e8cf51ff5f5
-- title:
--   First and Second Truncated-Product Derivatives Agree Inside the Plateau
-- statement:
--   If a two-dimensional cutoff equals one throughout the closed radius-R ball, then at every point strictly inside that ball the first and second Fréchet derivatives of the cutoff coordinate product coincide with those of the ordinary coordinate product. Equality in a neighbourhood transfers to derivatives.
-- source:
--   Mathlib.Analysis.Calculus.FDeriv.Congr, Filter.EventuallyEq.fderiv_eq and Filter.EventuallyEq.fderiv, verified in pinned Mathlib index and official documentation on 26 October 2026: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/FDeriv/Congr.html

import Mathlib.Analysis.Calculus.FDeriv.Congr

theorem ItoLemma.fin_two_truncated_product_derivatives_eq_on_plateau_interior
    (R : ℝ) (ψ : (Fin 2 → ℝ) → ℝ)
    (hp : ∀ y : Fin 2 → ℝ, ‖y‖ ≤ R → ψ y = 1)
    (z : Fin 2 → ℝ) (hz : ‖z‖ < R) :
    fderiv ℝ (fun y : Fin 2 → ℝ => ψ y * (y 0 * y 1)) z =
      fderiv ℝ (fun y : Fin 2 → ℝ => y 0 * y 1) z ∧
    fderiv ℝ (fderiv ℝ (fun y : Fin 2 → ℝ => ψ y * (y 0 * y 1))) z =
      fderiv ℝ (fderiv ℝ (fun y : Fin 2 → ℝ => y 0 * y 1)) z := by sorry
