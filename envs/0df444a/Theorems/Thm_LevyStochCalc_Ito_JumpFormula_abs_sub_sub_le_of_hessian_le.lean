-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_abs_sub_sub_le_of_hessian_le
-- name    : LevyStochCalc.Ito.JumpFormula.abs_sub_sub_le_of_hessian_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:21:20.415178+00:00
-- url     : https://prove2.me/theorems/d24c5fed-c0cc-4603-a88d-c43cbb34c627
-- title:
--   abs sub sub le of hessian le
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.abs_sub_sub_le_of_hessian_le` is extracted from `LevyStochCalc.Ito.JumpFormulaTaylorBounds`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaTaylorBounds_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Taylor bounds for the state increments of a `C²` function

For a function `u : ℝ → (Fin n → ℝ) → ℝ` of time and state that is `C²` jointly, the increment
`u(s, y + v) − u(s, y)` at a fixed time is controlled by a bound on the gradient, and the
first-order Taylor remainder `u(s, y + v) − u(s, y) − vᵀ∇u(s, y)` by a bound on the Hessian.
Both are mean value bounds: the first for `u(s, ·)` on the whole state space, the second for
`z ↦ u(s, z) − ∇u(s, y)ᵀ z` on the ball of radius `‖v‖` about `y`, where its derivative
`∇u(s, z) − ∇u(s, y)` is at most the Lipschitz constant of the gradient times `‖v‖`.

The hypotheses are the coordinatewise bounds on `gradient` and `hessian`, and the state space
carries the supremum norm, so the constants pick up the dimension: the operator norm of a
functional on `Fin n → ℝ` is at most the sum of its `n` coordinates, and that of a bilinear form
at most the sum of its `n²` coordinates.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.fderiv_apply_eq_sum_gradient` — the state derivative applied to
  a vector is the coordinate pairing with the gradient.
* `LevyStochCalc.Ito.JumpFormula.hessian_eq_fderiv_fderiv` — the Hessian is the second state
  derivative on the standard basis.
* `LevyStochCalc.Ito.JumpFormula.norm_fderiv_le_of_gradient_le`,
  `LevyStochCalc.Ito.JumpFormula.norm_fderiv_fderiv_le_of_hessian_le` — operator norm bounds on
  the first and second state derivatives from the coordinatewise bounds.
* `LevyStochCalc.Ito.JumpFormula.abs_sub_le_of_gradient_le` — the increment bound
  `|u(s, y + v) − u(s, y)| ≤ n K₁ ‖v‖`.
* `LevyStochCalc.Ito.JumpFormula.abs_sub_sub_le_of_hessian_le` — the remainder bound
  `|u(s, y + v) − u(s, y) − vᵀ∇u(s, y)| ≤ n² K₂ ‖v‖²`.
-/

namespace LevyStochCalc.Ito.JumpFormula

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}

section Derivatives

end Derivatives

section GradientBound

end GradientBound

section HessianBound

theorem _root_.LevyStochCalc.Ito.JumpFormula.abs_sub_sub_le_of_hessian_le (hu : ContDiff ℝ 2 (Function.uncurry u)) {K₂ : ℝ}
    (s : ℝ) (hK : ∀ z p q, |hessian u s z p q| ≤ K₂) (y v : Fin n → ℝ) :
    |u s (y + v) - u s y - ∑ i, v i * gradient u s y i| ≤ (n : ℝ) ^ 2 * K₂ * ‖v‖ ^ 2 := by sorry
