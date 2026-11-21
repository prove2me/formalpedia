-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_LevyDriver_integral_jointChaosStep_mul
-- name    : LevyStochCalc.Driver.LevyDriver.integral_jointChaosStep_mul
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T08:38:42.612479+00:00
-- url     : https://prove2.me/theorems/a676477b-349e-460c-9c0b-a5d0f0852644
-- title:
--   integral jointChaosStep mul
-- statement:
--   The source theorem `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStep_mul` is extracted from `LevyStochCalc.Driver.JointChaosStep`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointChaosStep_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The joint chaos element of one step of a Lévy driver

For a Lévy driver, a coordinate `j`, a step `(a, b]` and a mark set `A`, the bidegree-`(n, m)`
element of the step is the product `H_n(ΔWʲ; b - a) C_m(N(B); ν̂(B))` of the degree-`n` Wiener
chaos element of the increment `ΔWʲ = Wʲ_b - Wʲ_a` and the degree-`m` Poisson chaos element of
the strip `B = (a, b] ×ˢ A`. Since `σ(W)` and `σ(N)` are independent, the expectation of a
product of a function of the increment and a function of the count factors, so the `L²` pairing
of two such elements is the product of the Brownian and the Poisson pairings,
`E[J_(n, m) J_(n', m')] = δ_(n n') δ_(m m') n! τ ^ n m! λ ^ m` for `τ = b - a` and
`λ = (b - a) ν(A)`. Distinct bidegrees are therefore orthogonal, and a fortiori so are distinct
total degrees `n + m`. The step tuple is independent of the joint filtration at `a`, so the
conditional pairing at that node is the same constant.

One Brownian coordinate and one mark set are covered: these are polynomials of the single
increment `ΔWʲ` and the single count `N(B)`, with no mark profile beyond the indicator of `A`.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.jointChaosStep` — the bidegree-`(n, m)` element of a step.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.indepFun_increment_count` — a Brownian increment of the driver
  is independent of a count of its Poisson random measure.
* `LevyStochCalc.Driver.LevyDriver.integral_increment_count_mul` — the expectation of a product
  of a function of an increment and a function of a count factors.
* `LevyStochCalc.Driver.LevyDriver.memLp_two_jointChaosStep` — square integrability.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStep_mul` —
  `E[J_(n, m) J_(n', m')] = δ_(n n') δ_(m m') n! τ ^ n m! λ ^ m`.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStep_mul_eq_zero_of_add_ne` — orthogonality
  across total degrees.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStep_mul_eq_zero` — orthogonality across
  bidegrees.
* `LevyStochCalc.Driver.LevyDriver.condExp_jointChaosStep_mul` — the conditional pairing at the
  node preceding the step.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

section Independence

variable {γ δ : Type*} [MeasurableSpace γ] [MeasurableSpace δ]

end Independence

theorem _root_.LevyStochCalc.Driver.LevyDriver.integral_jointChaosStep_mul (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0}
    (hab : a ≤ b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (n m n' m' : ℕ) :
    ∫ ω, D.jointChaosStep j n m a b A ω * D.jointChaosStep j n' m' a b A ω ∂P
      = (if n = n' then (n.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ n else 0)
        * (if m = m' then (m.factorial : ℝ)
            * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ m else 0) := by sorry
