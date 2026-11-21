-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_LevyDriver_integral_coeffC_mul_jointChaosBlockC_mul
-- name    : LevyStochCalc.Driver.LevyDriver.integral_coeffC_mul_jointChaosBlockC_mul
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T10:24:14.056058+00:00
-- url     : https://prove2.me/theorems/393afff2-5f30-4671-bd90-fdefa81ac69b
-- title:
--   integral coeffC mul jointChaosBlockC mul
-- statement:
--   The source theorem `LevyStochCalc.Driver.LevyDriver.integral_coeffC_mul_jointChaosBlockC_mul` is extracted from `LevyStochCalc.Driver.JointChaosComplex`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointChaosComplex_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Complex-scaled total-degree blocks of a step of a Lévy driver

For a step `(a, b]` of a Lévy driver and a family of complex numbers indexed by the bidegrees and
constant in the sample point, the block of total degree `e` is the sum, over the bidegrees
`(n, m)` with `n + m = e`, of the joint chaos elements of that bidegree scaled by those numbers.
Such a block is square integrable over a mark set of finite intensity, its complex conjugate is
the block of the conjugate scalars, and blocks of different total degree are orthogonal; at equal
total degree the bilinear pairing and the second moment of the modulus are the bidegree sums of
the products of the scalars against `n! τ ^ n m! λ ^ m`, for `τ = b - a` and `λ = (b - a) ν(A)`.
Against a bounded complex coefficient strongly measurable for the joint filtration at `a`, the
node preceding the step, the pairing of two joint chaos elements, and hence of two blocks, is the
mean of the coefficient times the bidegree pairing. Through `(ℑz)² = (‖z‖² − ℜ z²)/2` that
factorisation turns into the second moment of the imaginary part of the product of such a
coefficient with a block, read off the second moments of the two factors.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.jointChaosBlockC` — the block of total degree `e` of a step at
  complex scalars.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosBlockC_mul` — the pairing of two
  complex-scaled blocks of a step.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosBlockC_sq` — the bilinear second moment of
  a complex-scaled block.
* `LevyStochCalc.Driver.LevyDriver.integral_norm_sq_jointChaosBlockC` — the second moment of the
  modulus of a complex-scaled block.
* `LevyStochCalc.Driver.LevyDriver.integral_coeffC_mul_jointChaosBlockC_mul` — the pairing of two
  complex-scaled blocks against a bounded complex coefficient measurable at the node preceding
  the step.
* `LevyStochCalc.Driver.LevyDriver.integral_sq_im_coeffC_mul_jointChaosBlockC` — the second
  moment of the imaginary part of such a coefficient times a block.
-/

namespace LevyStochCalc.Driver.LevyDriver

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability LevyStochCalc.Poisson Finset
open scoped NNReal ENNReal

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {P : Measure Ω}
  [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

theorem _root_.LevyStochCalc.Driver.LevyDriver.integral_coeffC_mul_jointChaosBlockC_mul (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a < b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {Q : Ω → ℂ} (hQ : StronglyMeasurable[D.filtration (a : ℝ)] Q) {Cb : ℝ}
    (hQb : ∀ ω, ‖Q ω‖ ≤ Cb) (c c' : ℕ × ℕ → ℂ) (e e' : ℕ) :
    ∫ ω, Q ω * (jointChaosBlockC D j a b A c e ω * jointChaosBlockC D j a b A c' e' ω) ∂P
      = (∫ ω, Q ω ∂P) * (if e = e' then ∑ p ∈ antidiagonal e, c p * c' p
          * ((((p.1.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ p.1)
              * ((p.2.factorial : ℝ) * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ p.2) : ℝ) : ℂ)
        else 0) := by sorry
