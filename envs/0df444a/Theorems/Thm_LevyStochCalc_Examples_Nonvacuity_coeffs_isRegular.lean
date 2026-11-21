-- Prove2me | Theorems.Thm_LevyStochCalc_Examples_Nonvacuity_coeffs_isRegular
-- name    : LevyStochCalc.Examples.Nonvacuity.coeffs_isRegular
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T23:36:45.584185+00:00
-- url     : https://prove2.me/theorems/a4b11623-edea-426f-a993-2799108a5eb1
-- title:
--   coeffs isRegular
-- statement:
--   The source theorem `LevyStochCalc.Examples.Nonvacuity.coeffs_isRegular` is extracted from `NonvacuityItoLevy`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_NonvacuityItoLevy_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A jump diffusion satisfying the hypotheses of the Itô–Lévy formula

The scalar jump diffusion `dX_t = dW_t + ∫_ℝ e Ñ(dt, de)` with `X_0 = 0`, driven by a
one-dimensional Brownian motion and a Poisson random measure of intensity `dt ⊗ δ_1` on
`[0, ∞) × ℝ`, together with the state function `u(t, x) = x₀²` on the horizon `[0, 1]`.

The coefficients `μ = 0`, `σ = 1`, `γ(s, x, e) = e` are regular and Lipschitz with constant
`0`, so the SDE has a solution, and `u` is `C²` with gradient `∇u(s, x) = 2x₀`, diffusion
integrand `(∇u)ᵀσ = 2x₀`, jump increment `u(x + e) − u(x) = 2ex₀ + e²` and compensator drift
`u(x + e) − u(x) − e∇u(x) = e²`. The derived energies are finite because the solution has a
finite `S²` norm on every window, and the compensator drift is the constant `1`.

The gradient of `u` is unbounded, so `u` lies outside the range of the Itô–Lévy formula for a
state function with bounded first and second derivatives.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.JumpFormula

/-! ### The model -/

/-! ### Regularity of the coefficients -/

theorem _root_.LevyStochCalc.Examples.Nonvacuity.coeffs_isRegular : coeffs.IsRegular jumpIntensity := by sorry
