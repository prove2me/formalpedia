-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_LevyDriver_memLp_two_jointChaosStepProfileC
-- name    : LevyStochCalc.Driver.LevyDriver.memLp_two_jointChaosStepProfileC
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T16:30:13.683161+00:00
-- url     : https://prove2.me/theorems/af984f63-ae6f-42d9-aa67-b4c1bf8248fc
-- title:
--   memLp two jointChaosStepProfileC
-- statement:
--   The source theorem `LevyStochCalc.Driver.LevyDriver.memLp_two_jointChaosStepProfileC` is extracted from `LevyStochCalc.Driver.JointChaosProfileComplex`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointChaosProfileComplex_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Complex joint chaos elements of a step at a mark profile, across mark families

For a Lévy driver, a coordinate `j`, a step `(a, b]` with `τ = b − a`, a finite pairwise
disjoint family `A` of mark sets of finite intensity and a complex profile `c` constant on each of
them, the complex bidegree-`(r, s)` element of the step is `X_(r, s)(c; A) = H_r(ΔWʲ; τ) D_s(c)`,
the product of the degree-`r` Wiener chaos element of the increment and the degree-`s` element of
the profile over the strips `(a, b] ×ˢ A k`. The Brownian and the Poisson factors are independent,
so the bilinear moment of two such elements over different families `A`, `A'` factors into the
Hermite and the Charlier Gram across the families,

  `E[X_(r, s)(c; A) X_(r', s')(c'; A')] = δ_(r r') r! τ ^ r δ_(s s') s! (τ ⟨c, c'⟩) ^ s`,

with `⟨c, c'⟩ = ∑_(k, l) c_k c'_l ν(A k ∩ A' l)`; distinct bidegrees, and a fortiori distinct total
degrees, are orthogonal whatever the two families. Every element of the step is measurable for
the σ-algebra of the step over the strips of both families, which is independent of the joint
filtration at `a`, and also of the augmentation of its join with an initial σ-algebra independent
of the whole filtration. So against a coefficient measurable for such a node σ-algebra the pairing
of two elements is the mean of the coefficient times their pairing, and the conditional pairing
given the node σ-algebra is the constant pairing.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.jointChaosStepProfileC` — the complex bidegree-`(r, s)` element.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.memLp_two_jointChaosStepProfileC` — square integrability.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfileC_mul_cross`,
  `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfileC_mul_conj_cross` — the bidegree
  Gram across two mark families.
* `LevyStochCalc.Driver.LevyDriver.indep_stepSigma_filtration`,
  `LevyStochCalc.Driver.LevyDriver.indep_stepSigma_aug_sup` — the σ-algebra of the step is
  independent of the joint filtration at the node, and of the augmentation of its join with an
  independent initial σ-algebra.
* `LevyStochCalc.Driver.LevyDriver.integral_mul_eq_mul_integral_of_indep_stepSigma` — the pairing
  of a variable of the step against a coefficient measurable at the node.
* `LevyStochCalc.Driver.LevyDriver.integral_coeff_mul_jointChaosStepProfileC_mul_conj` — the
  same for the Hermitian pairing of two elements over different families.
* `LevyStochCalc.Driver.LevyDriver.condExp_jointChaosStepProfileC_mul_conj` — the conditional
  Hermitian pairing at the node is the constant Gram.
-/

namespace LevyStochCalc.Driver.LevyDriver

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability LevyStochCalc.Poisson Finset
  Filter
open scoped NNReal ENNReal Topology

universe u v w

section Elements

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {P : Measure Ω}
  [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Measurability -/

/-! ### The complex bidegree element -/

theorem _root_.LevyStochCalc.Driver.LevyDriver.memLp_two_jointChaosStepProfileC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (r s : ℕ)
    (c : Fin p → ℂ) :
    MemLp (D.jointChaosStepProfileC j r s a b A c) 2 P := by sorry
