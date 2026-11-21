-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_LevyDriver_integral_jointChaosStepProfile_mul
-- name    : LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfile_mul
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T09:05:34.764238+00:00
-- url     : https://prove2.me/theorems/d02d66e1-583b-4f4e-8100-540581eb6352
-- title:
--   integral jointChaosStepProfile mul
-- statement:
--   The source theorem `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfile_mul` is extracted from `LevyStochCalc.Driver.JointChaosProfile`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointChaosProfile_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The joint chaos element of one step of a Lévy driver at a simple mark profile

For a Lévy driver, a coordinate `j`, a step `(a, b]` and a finite pairwise disjoint family `A` of
mark sets of finite intensity carrying a profile `c` constant on each of them, the
bidegree-`(n, m)` element of the step is the product `H_n(ΔWʲ; b - a) D_m(c)` of the degree-`n`
Wiener chaos element of the increment `ΔWʲ = Wʲ_b - Wʲ_a` and the degree-`m` chaos element of the
profile over the strips `(a, b] ×ˢ A k`. Since `σ(W)` and `σ(N)` are independent, the expectation
of a product of a function of the increment and a function of the counts of the strips factors,
so the `L²` pairing of two such elements is the product of the Hermite and the Charlier factor,
`E[J_(n, m)(c) J_(n', m')(c')] = δ_(n n') δ_(m m') n! τ ^ n m! ⟨c, c'⟩ ^ m` for `τ = b - a` and
the bilinear form `⟨c, c'⟩ = ∑_k c_k c'_k τ ν(A k)`. Distinct bidegrees are therefore orthogonal,
and a fortiori so are distinct total degrees `n + m`. The step tuple is independent of the joint
filtration at `a`, so the conditional pairing at that node is the same constant.

One Brownian coordinate is covered, and the profile is constant on the sets of one given family:
no mode of `L²(ν)` beyond such combinations of indicators enters. On a one-set family the element
is the single-mark-set element of a step scaled by `c 0 ^ m`.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.jointChaosStepProfile` — the bidegree-`(n, m)` element of a
  step at a mark profile.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.measurable_markedChaosDegree_sigmaPoisson` — a degree element
  of a profile is measurable for the Poisson σ-algebra of the driver.
* `LevyStochCalc.Driver.LevyDriver.indepFun_increment_markedChaosDegree` — a Brownian increment
  of the driver is independent of a degree element of a profile of its Poisson random measure.
* `LevyStochCalc.Driver.LevyDriver.memLp_two_jointChaosStepProfile` — square integrability.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfile_mul` —
  `E[J_(n,m)(c) J_(n',m')(c')] = δ_(n n') δ_(m m') n! τ ^ n m! ⟨c, c'⟩ ^ m`.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfile_sq` — the second moment as the
  product of the Hermite and the Charlier factor.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfile_mul_eq_zero`,
  `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfile_mul_eq_zero_of_add_ne` —
  orthogonality across bidegrees and across total degrees.
* `LevyStochCalc.Driver.LevyDriver.condExp_jointChaosStepProfile_mul` — the conditional pairing
  at the node preceding the step.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Independence of the Brownian and the Poisson data of a step -/

namespace LevyDriver

/-! ### The element of a bidegree at a mark profile -/

theorem _root_.LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfile_mul (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (n m n' m' : ℕ)
    (c c' : Fin p → ℝ) :
    ∫ ω, D.jointChaosStepProfile j n m a b A c ω
        * D.jointChaosStepProfile j n' m' a b A c' ω ∂P
      = (if n = n' then (n.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ n else 0)
        * (if m = m' then (m.factorial : ℝ)
            * (∑ k, c k * c' k * (((b : ℝ) - (a : ℝ)) * (ν (A k)).toReal)) ^ m else 0) := by sorry
