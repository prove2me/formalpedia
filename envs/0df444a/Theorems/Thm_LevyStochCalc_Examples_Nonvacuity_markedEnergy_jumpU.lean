-- Prove2me | Theorems.Thm_LevyStochCalc_Examples_Nonvacuity_markedEnergy_jumpU
-- name    : LevyStochCalc.Examples.Nonvacuity.markedEnergy_jumpU
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:56:18.200197+00:00
-- url     : https://prove2.me/theorems/3f8530ba-80b0-45af-ab96-c2b04c1cb5aa
-- title:
--   markedEnergy jumpU
-- statement:
--   The source theorem `LevyStochCalc.Examples.Nonvacuity.markedEnergy_jumpU` is extracted from `NonvacuityBSDEJJump`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_NonvacuityBSDEJJump_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A backward equation with jumps whose jump integrand carries positive energy

The scalar backward equation

  `Y_t = ξ − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

driven by a Lévy driver with one Brownian coordinate and a Poisson random measure of intensity
`dt ⊗ δ_1` on `[0, ∞) × ℝ`. The generator vanishes, the horizon is `T = 1`, the jump integrand
is the window indicator `1_{(0, 1]}`, constant in the mark, and the terminal datum is its
compensated integral over the whole horizon, so the value process is that compensated integral
and the Brownian integrand is `0`.

## Main statements

* `exists_solvesBSDEJ_jump` — the equation is solved by a càdlàg version of the compensated
  integral of `1_{(0, 1]}` together with the integrand pair `(0, 1_{(0, 1]})`.
* `markedEnergy_jumpU` — the marked energy of `1_{(0, 1]}` on `[0, 1]` for the intensity `δ_1`
  is `1`.
* `markedEnergy_eq_one_of_solvesBSDEJ` — every solution triple of the equation has jump
  integrand of marked energy `1` on `[0, 1]`.
* `exists_solvesBSDEJ_markedEnergy_ne_zero` — on a probability space carrying such a driver the
  equation has a solution triple and every solution triple has jump integrand of nonzero marked
  energy on the horizon.

## References

* Tang–Li, *Necessary conditions for optimal control of stochastic systems with random jumps*,
  SIAM J. Control Optim. 32 (1994), §2.
* Delong, *BSDEs with Jumps and their Actuarial and Financial Applications*, Springer 2013,
  §4.1.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.BSDEJ.Solves
open LevyStochCalc.Driver (LevyDriver)

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The integrands of the equation -/

section Fields

variable (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))

theorem _root_.LevyStochCalc.Examples.Nonvacuity.markedEnergy_jumpU :
    Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
      (fun ω s e => jumpU Ω s ω e) = 1 := by sorry
