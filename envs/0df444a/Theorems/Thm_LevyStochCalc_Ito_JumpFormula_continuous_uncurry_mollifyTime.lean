-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_continuous_uncurry_mollifyTime
-- name    : LevyStochCalc.Ito.JumpFormula.continuous_uncurry_mollifyTime
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:59:03.074265+00:00
-- url     : https://prove2.me/theorems/6e3819f0-8c92-403d-8a94-38bdd51df079
-- title:
--   continuous uncurry mollifyTime
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.continuous_uncurry_mollifyTime` is extracted from `LevyStochCalc.Ito.C12Mollify`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_C12Mollify_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Mollification in time of a function of time and state

For a function `u : ℝ → (Fin n → ℝ) → ℝ` of time and state and a smooth compactly supported bump
`ρ` on `ℝ`, the time mollification `mollifyTime u ρ t x = ∫ r, ρ(r) u(t - r, x) dr` averages `u`
over a window of time of width the outer radius of `ρ`, leaving the state argument untouched. At
a fixed state it is the convolution of the normalised bump with the time section `r ↦ u(r, x)`,
so it inherits the smoothness of the bump in the time variable; it is jointly continuous in time
and state whenever `u` is; and along a family of bumps whose outer radii tend to `0` it converges
to `u` pointwise.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.mollifyTime_apply_eq_convolution` — the time mollification at a
  fixed state is a convolution.
* `LevyStochCalc.Ito.JumpFormula.contDiff_time_mollifyTime` — at a fixed state the time
  mollification is `C^N` in time for every `N`.
* `LevyStochCalc.Ito.JumpFormula.continuous_uncurry_mollifyTime` — the time mollification of a
  jointly continuous function is jointly continuous.
* `LevyStochCalc.Ito.JumpFormula.tendsto_mollifyTime` — pointwise convergence of the time
  mollification along a family of bumps whose outer radii tend to `0`.
* `LevyStochCalc.Ito.JumpFormula.timeDeriv_mollifyTime`,
  `LevyStochCalc.Ito.JumpFormula.gradient_mollifyTime`,
  `LevyStochCalc.Ito.JumpFormula.hessian_mollifyTime` — the time derivative, the gradient and the
  Hessian of the time mollification of a `C^{1,2}` function are the time mollifications of the
  time derivative, the gradient and the Hessian of that function.
-/

open MeasureTheory Filter Topology
open scoped Convolution

namespace LevyStochCalc.Ito.JumpFormula

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}

theorem _root_.LevyStochCalc.Ito.JumpFormula.continuous_uncurry_mollifyTime (hu : Continuous (Function.uncurry u))
    (ρ : ContDiffBump (0 : ℝ)) : Continuous (Function.uncurry (mollifyTime u ρ)) := by sorry
