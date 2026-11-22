-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_exists_bound_on_box_c12
-- name    : LevyStochCalc.Ito.JumpFormula.exists_bound_on_box_c12
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T12:41:40.351205+00:00
-- url     : https://prove2.me/theorems/3b38698c-5894-4d3b-bb01-d42f6f2d41e1
-- title:
--   exists bound on box c12
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.exists_bound_on_box_c12` is extracted from `LevyStochCalc.Ito.JumpFormulaContinuityC12`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaContinuityC12_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Derivative bounds for a `C^{1,2}` state function

For a function `u : ℝ → (Fin n → ℝ) → ℝ` of class `C^{1,2}` the state section `u s` is `C²`, so
the mean value bounds of a jointly `C²` function of time and state hold verbatim: the increment
`u(s, y + v) − u(s, y)` is controlled by a coordinatewise bound on the gradient and the
first-order Taylor remainder `u(s, y + v) − u(s, y) − vᵀ∇u(s, y)` by a coordinatewise bound on
the Hessian. The mixed jump increment and the mixed compensator-drift integrand inherit those
bounds, and the joint continuity of the time derivative, the gradient and the Hessian bounds all
three by one constant on a compact time–space box.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.abs_sub_le_of_gradient_le_c12` — the increment bound
  `|u(s, y + v) − u(s, y)| ≤ n K₁ ‖v‖` for a `C^{1,2}` function.
* `LevyStochCalc.Ito.JumpFormula.abs_sub_sub_le_of_hessian_le_c12` — the remainder bound
  `|u(s, y + v) − u(s, y) − vᵀ∇u(s, y)| ≤ n² K₂ ‖v‖²` for a `C^{1,2}` function.
* `LevyStochCalc.Ito.JumpFormula.abs_mixedJumpIncrement_le_c12`,
  `LevyStochCalc.Ito.JumpFormula.abs_mixedCompensatorDriftIntegrand_le_c12` — the bounds on the
  mixed jump increment and the mixed compensator-drift integrand of a `C^{1,2}` function.
* `LevyStochCalc.Ito.JumpFormula.exists_bound_on_box_c12` — on `[a, b] × closedBall 0 R` the time
  derivative, every gradient entry and every Hessian entry of a `C^{1,2}` function are bounded by
  one constant.
-/

namespace LevyStochCalc.Ito.JumpFormula

universe v

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}

section Derivatives

end Derivatives

section GradientBound

end GradientBound

section HessianBound

end HessianBound

section MixedBounds

variable {E : Type v}

end MixedBounds

section BoxBounds

theorem _root_.LevyStochCalc.Ito.JumpFormula.exists_bound_on_box_c12 (hu : IsC12 u) (a b R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ s x, s ∈ Set.Icc a b → ‖x‖ ≤ R → |timeDeriv u s x| ≤ K) ∧
      (∀ s x, s ∈ Set.Icc a b → ‖x‖ ≤ R → ∀ i, |gradient u s x i| ≤ K) ∧
      (∀ s x, s ∈ Set.Icc a b → ‖x‖ ≤ R → ∀ i j, |hessian u s x i j| ≤ K) := by sorry
