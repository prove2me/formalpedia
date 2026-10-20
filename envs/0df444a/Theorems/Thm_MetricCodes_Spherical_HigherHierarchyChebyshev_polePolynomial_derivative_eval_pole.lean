-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_polePolynomial_derivative_eval_pole
-- name    : MetricCodes.Spherical.HigherHierarchyChebyshev.polePolynomial_derivative_eval_pole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:31.984834+00:00
-- url     : https://prove2.me/theorems/4d893612-3f4c-4257-8f01-bbb421168816
-- title:
--   MetricCodes.Spherical.HigherHierarchyChebyshev.polePolynomial_derivative_eval_pole
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev

theorem MetricCodes.Spherical.HigherHierarchyChebyshev.polePolynomial_derivative_eval_pole
    (R : ℝ) (r : ℕ) (ℓ : Fin (r + 1)) :
    (polePolynomial R (r + 1)).derivative.eval
        (pole R (r + 1) ℓ.val) =
      ∏ m : Fin r,
        (pole R (r + 1) ℓ.val -
          pole R (r + 1) (ℓ.succAbove m).val) := by sorry
