-- Prove2me | Theorems.Thm_LevyStochCalc_Examples_Nonvacuity_integral_sq_solvesOn_one
-- name    : LevyStochCalc.Examples.Nonvacuity.integral_sq_solvesOn_one
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:11:11.796272+00:00
-- url     : https://prove2.me/theorems/ec07e299-7a7b-4c19-b371-b738ba270a42
-- title:
--   integral sq solvesOn one
-- statement:
--   The source theorem `LevyStochCalc.Examples.Nonvacuity.integral_sq_solvesOn_one` is extracted from `NonvacuityItoLevyPath`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardGlobal_F002
import Definitions.Def_LevyStochCalc_Ito_PicardWindow_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoRange_F000
import Definitions.Def_LevyStochCalc_Probability_Progressive_F000
import Definitions.Def_NonvacuityItoLevyPath_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The value at time `1` of the jump diffusion `dX_t = dW_t + ∫_ℝ e Ñ(dt, de)`

For the coefficients `coeffs` (`μ = 0`, `σ = 1`, `γ(s, x, e) = e`) and the jump intensity
`δ₁`, a path solving the jump-diffusion integral equation from `0` relative to a filtration
carrying both driver properties has second moment `2` in its single coordinate at time `1`:
the drift vanishes, the Brownian leg contributes `∫_0^1 1 ds = 1`, the compensated leg
contributes `∫_0^1 ∫_ℝ e² δ₁(de) ds = 1`, and the two legs are orthogonal. In particular that
coordinate is not almost surely `0` at time `1`.

The second moment is the expectation form of the quadratic Itô formula,
`LevyStochCalc.Ito.SecondMoment.integral_mul_self_eq_of_isItoLevyProcess`, whose orthogonality
input is a cross witness for the filtration; `crossWitnessAugRightCont` carries the driver's
own witness to the augmented right-continuation of the joint filtration, the filtration at
which `LevyStochCalc.Ito.Picard.exists_globalSolution` produces a solution.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.Driver (LevyDriver)
open LevyStochCalc.Ito.Picard (SolvesOn eqn_sum_form )
open LevyStochCalc.Ito.Setting (IsItoLevyProcess)

universe u v

/-! ### A cross witness at the augmented right-continuation -/

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The second moment of a solution at time `1` -/

section Solution

variable {D : LevyDriver P 1 jumpIntensity}
  {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin 1, Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : Poisson.IsPoissonFiltration D.N ℱ} {X : ℝ → Ω → (Fin 1 → ℝ)}

theorem _root_.LevyStochCalc.Examples.Nonvacuity.integral_sq_solvesOn_one (𝒲 : D.CrossWitness ℱ)
    (hXm : Measurable (Function.uncurry X))
    (hXsol : ∀ T : ℝ, SolvesOn D.W D.N ℱ hℱW hℱN coeffs (0 : Fin 1 → ℝ) X T) :
    ∫ ω, X 1 ω 0 * X 1 ω 0 ∂P = 2 := by sorry
