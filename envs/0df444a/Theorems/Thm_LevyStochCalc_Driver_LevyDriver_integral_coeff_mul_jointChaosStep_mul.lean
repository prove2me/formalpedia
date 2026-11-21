-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_LevyDriver_integral_coeff_mul_jointChaosStep_mul
-- name    : LevyStochCalc.Driver.LevyDriver.integral_coeff_mul_jointChaosStep_mul
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T08:43:01.033382+00:00
-- url     : https://prove2.me/theorems/5ccf45e7-64d6-427f-829d-79e4e80578d7
-- title:
--   integral coeff mul jointChaosStep mul
-- statement:
--   The source theorem `LevyStochCalc.Driver.LevyDriver.integral_coeff_mul_jointChaosStep_mul` is extracted from `LevyStochCalc.Driver.JointChaosBlock`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointChaosStep_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Total-degree blocks of a step of a Lévy driver

For a step `(a, b]` with `a < b` and a coefficient `c` bounded and strongly measurable for the
joint filtration at `a`, the node preceding the step, the pairing `E[c J_(n, m) J_(n', m')]` of
two joint chaos elements of the step weighted by `c` is the mean `E[c]` of the coefficient times
the bidegree pairing `δ_(n n') δ_(m m') n! τ ^ n m! λ ^ m`, for `τ = b - a` and
`λ = (b - a) ν(A)`; elements of different bidegree therefore stay orthogonal against such a
coefficient. The block of total degree `e` is the sum over the bidegrees `(n, m)` with `n + m = e`
of the elements of that bidegree weighted by such coefficients, and two blocks of different total
degree are orthogonal in `L²(P)`.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.jointChaosBlock` — the block of total degree `e` of a step.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.integral_coeff_mul_jointChaosStep_mul` — the pairing of two
  elements of a step weighted by a bounded coefficient measurable at the node preceding the step
  is the mean of the coefficient times the bidegree pairing.
* `LevyStochCalc.Driver.LevyDriver.integral_coeff_mul_jointChaosStep_mul_eq_zero` — orthogonality
  across bidegrees against such a coefficient.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosBlock_mul_eq_zero` — orthogonality of two
  blocks of different total degree.
-/

namespace LevyStochCalc.Driver.LevyDriver

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability LevyStochCalc.Poisson
open scoped NNReal ENNReal

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {P : Measure Ω}
  [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

theorem _root_.LevyStochCalc.Driver.LevyDriver.integral_coeff_mul_jointChaosStep_mul (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a < b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {c : Ω → ℝ} (hc : StronglyMeasurable[D.filtration (a : ℝ)] c) {Cb : ℝ}
    (hcb : ∀ ω, ‖c ω‖ ≤ Cb) (n m n' m' : ℕ) :
    ∫ ω, c ω * (D.jointChaosStep j n m a b A ω * D.jointChaosStep j n' m' a b A ω) ∂P
      = (∫ ω, c ω ∂P)
        * ((if n = n' then (n.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ n else 0)
          * (if m = m' then (m.factorial : ℝ)
              * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ m else 0)) := by sorry
