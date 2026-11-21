-- Prove2me | Theorems.Thm_LevyStochCalc_Examples_Nonvacuity_exists_solvesBSDEJ_windowZ
-- name    : LevyStochCalc.Examples.Nonvacuity.exists_solvesBSDEJ_windowZ
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:16:27.667244+00:00
-- url     : https://prove2.me/theorems/3793b91b-fc88-480c-91c1-736b081e558f
-- title:
--   exists solvesBSDEJ windowZ
-- statement:
--   The source theorem `LevyStochCalc.Examples.Nonvacuity.exists_solvesBSDEJ_windowZ` is extracted from `NonvacuityBSDEJZ`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_SupBound_F000
import Definitions.Def_LevyStochCalc_Brownian_MultidimIto_F000
import Definitions.Def_LevyStochCalc_Driver_JointFiltration_F000
import Definitions.Def_NonvacuityBSDEJZ_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A backward equation with jumps whose Brownian integrand carries positive energy

The scalar backward equation

  `Y_t = W_1 − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

driven by a Lévy driver with one Brownian coordinate and a Poisson random measure of intensity
`dt ⊗ δ_1` on `[0, ∞) × ℝ`. The generator vanishes, the horizon is `T = 1` and the terminal
datum is the Brownian value `W_1`, so the value process is the Brownian motion itself, the
Brownian integrand is the indicator `1_{(0, 1]}` of the horizon and the jump integrand is `0`.

## Main statements

* `exists_solvesBSDEJ_windowZ` — the equation is solved by a continuous modification of the
  Brownian motion together with the integrand pair `(1_{(0, 1]}, 0)`.
* `energy_windowZ` — the energy of `1_{(0, 1]}` on `[0, 1]` is `1`.
* `energy_eq_one_of_solvesBSDEJ` — every solution triple of the equation has Brownian integrand
  of energy `1` on `[0, 1]`.
* `exists_solvesBSDEJ_energy_ne_zero` — on a probability space carrying such a driver the
  equation has a solution triple and every solution triple has Brownian integrand of nonzero
  energy.

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

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The integrands of the equation -/

section Fields

variable (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))

end Fields

/-! ### A solution triple with the indicator integrand -/

theorem _root_.LevyStochCalc.Examples.Nonvacuity.exists_solvesBSDEJ_windowZ (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) :
    ∃ Y : ℝ → Ω → ℝ,
      SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (fun ω => (D.W.W 0).W 1 ω) 1 Y (windowZ Ω)
          (fun _ _ _ => (0 : ℝ)) ∧
        ∀ t, Y t =ᵐ[P] fun ω => (D.W.W 0).W t ω := by sorry
