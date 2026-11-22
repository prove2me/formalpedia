-- Prove2me | Theorems.Thm_LevyStochCalc_Examples_Nonvacuity_exists_solvesBSDEJ_expZ
-- name    : LevyStochCalc.Examples.Nonvacuity.exists_solvesBSDEJ_expZ
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T09:09:36.527068+00:00
-- url     : https://prove2.me/theorems/ae0ab247-c7fb-4956-b5e2-9df77b3381cb
-- title:
--   exists solvesBSDEJ expZ
-- statement:
--   The source theorem `LevyStochCalc.Examples.Nonvacuity.exists_solvesBSDEJ_expZ` is extracted from `NonvacuityBSDEJExp`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_SupBound_F000
import Definitions.Def_LevyStochCalc_BSDEJ_SupBound_F002
import Definitions.Def_NonvacuityBSDEJExp_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The explicit solution of a backward equation with the identity generator

The scalar backward equation

  `Y_t = W_1 + ∫_t^1 Y_s ds − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

driven by a Lévy driver with one Brownian coordinate and a Poisson random measure of intensity
`dt ⊗ δ_1` on `[0, ∞) × ℝ`. The generator is `f(s, y, z, u) = y`, the horizon is `T = 1` and the
terminal datum is the Brownian value `W_1`. Since `d(e^{1-t} W_t) = −e^{1-t} W_t dt + e^{1-t} dW_t`,
the value process is `Y_t = e^{1-t} W_t`, the Brownian integrand is the windowed weight
`e^{1-s} 1_{(0, 1]}(s)` and the jump integrand vanishes.

## Main statements

* `exists_solvesBSDEJ_expZ` — the equation is solved by `e^{1-t}` times a continuous modification
  of the Brownian motion, together with the integrand pair `(e^{1-s} 1_{(0, 1]}, 0)`.
* `energy_expZ` — the energy of `e^{1-s} 1_{(0, 1]}` on `[0, 1]` is `(e² − 1)/2`.
* `energy_eq_of_solvesBSDEJ` — every solution triple of the equation has Brownian integrand of
  energy `(e² − 1)/2` on `[0, 1]`.
* `exists_solvesBSDEJ_generator_id_energy_ne_zero` — on a probability space carrying such a
  driver the equation has this solution triple and every solution triple has Brownian integrand
  of nonzero energy.

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
open LevyStochCalc.Brownian.Ito (IsVectorItoVersion)

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The test function `(t, x) ↦ e^{1-t} x` -/

/-! ### The exponential weight -/

/-! ### The integrands of the equation -/

/-! ### Itô's formula for `e^{1-t} W_t` -/

section Version

variable (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))

end Version

/-! ### The solution triple -/

theorem _root_.LevyStochCalc.Examples.Nonvacuity.exists_solvesBSDEJ_expZ (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) :
    ∃ Y : ℝ → Ω → ℝ,
      SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y (expZ Ω)
          (fun _ _ _ => (0 : ℝ)) ∧
        ∀ t, Y t =ᵐ[P] fun ω => Real.exp (1 - t) * (D.W.W 0).W t ω := by sorry
