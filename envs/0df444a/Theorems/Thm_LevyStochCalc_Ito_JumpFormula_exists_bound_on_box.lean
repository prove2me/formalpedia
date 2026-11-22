-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_exists_bound_on_box
-- name    : LevyStochCalc.Ito.JumpFormula.exists_bound_on_box
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:58:45.564926+00:00
-- url     : https://prove2.me/theorems/8555631f-8312-4b10-b15c-ccd84951ccbe
-- title:
--   exists bound on box
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.exists_bound_on_box` is extracted from `LevyStochCalc.Ito.LocalDerivBounds`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_LocalDerivBounds_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Local bounds on the derivatives of a `C²` state function

A `C²` function of time and state has continuous time derivative, gradient and Hessian, so on a
compact time–space box each of them is bounded. `exists_bound_on_box` packages the three bounds
as a single constant, and `exists_bound_on_box_of_le` reads it along a path confined to a ball.

These are the local replacements for the global derivative bounds of the bounded-derivative
Itô–Lévy formula: where that theorem asks `|∂ₜu| ≤ K₀`, `|∇u| ≤ K₁` and `|∇²u| ≤ K₂` everywhere,
a path stopped on leaving a ball only meets the state function on a compact box, where the same
bounds hold for free.

## Main statements

* `exists_bound_on_box` — on `[a, b] × closedBall 0 R` the time derivative, every gradient entry
  and every Hessian entry of a `C²` function are bounded by one constant.
-/

open MeasureTheory Filter Topology

namespace LevyStochCalc.Ito.JumpFormula

universe u

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}

theorem _root_.LevyStochCalc.Ito.JumpFormula.exists_bound_on_box (hu : ContDiff ℝ 2 (Function.uncurry u)) (a b R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ s x, s ∈ Set.Icc a b → ‖x‖ ≤ R → |timeDeriv u s x| ≤ K) ∧
      (∀ s x, s ∈ Set.Icc a b → ‖x‖ ≤ R → ∀ i, |gradient u s x i| ≤ K) ∧
      (∀ s x, s ∈ Set.Icc a b → ‖x‖ ≤ R → ∀ i j, |hessian u s x i j| ≤ K) := by sorry
