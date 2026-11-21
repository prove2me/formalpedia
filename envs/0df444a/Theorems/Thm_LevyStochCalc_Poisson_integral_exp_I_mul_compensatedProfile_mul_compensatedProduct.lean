-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_integral_exp_I_mul_compensatedProfile_mul_compensatedProduct
-- name    : LevyStochCalc.Poisson.integral_exp_I_mul_compensatedProfile_mul_compensatedProduct
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:06:51.226045+00:00
-- url     : https://prove2.me/theorems/aa15c27a-fe27-4ad6-950e-cb65cb443ac4
-- title:
--   integral exp I mul compensatedProfile mul compensatedProduct
-- statement:
--   The source theorem `LevyStochCalc.Poisson.integral_exp_I_mul_compensatedProfile_mul_compensatedProduct` is extracted from `LevyStochCalc.Poisson.ProfileExpProduct`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ProfileExpPairing_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pairing of the character of a compensated profile integral with a compensated product

For mark profiles `f, g` whose product is square integrable, the compensated product over the
step `(a, b]` is `Q(f, g) = J(f) J(g) − J(f g) − (b − a) ∫ f g dν`, with `J` the compensated
integral over the step. For a square-integrable profile `h`, a real frequency `u` and
`γ_u = e^{iuh} − 1`,

  `E[e^{iuJ(h)} Q(f, g)] = (b − a)² ∫ γ_u f dν ∫ γ_u g dν · E[e^{iuJ(h)}]`.

It is the second-order pairing `E[e^{iuJ(h)} J(f) J(g)]` less the first-order pairing with
`J(f g)` and the constant: the diagonal term `(b − a) ∫ e^{iuh} f g dν` of the former splits as
`(b − a) ∫ γ_u f g dν`, the pairing with `J(f g)`, plus `(b − a) ∫ f g dν`, the constant. The
profile `h` is only square integrable; `f g` is square integrable when one of the two profiles is
bounded.

## Main statements

* `LevyStochCalc.Poisson.integral_exp_I_mul_compensatedProfile_mul_compensatedProduct` — the
  pairing with the compensated product.
* `LevyStochCalc.Poisson.integral_exp_I_mul_compensatedProfile_mul_compensatedProduct_of_bound`
  — the same when one of the two profiles is bounded.
-/

open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

theorem _root_.LevyStochCalc.Poisson.integral_exp_I_mul_compensatedProfile_mul_compensatedProduct
    (N : PoissonRandomMeasure P ν) {h f g : E → ℝ} (hh : MemLp h 2 ν) (hf : MemLp f 2 ν)
    (hg : MemLp g 2 ν) (hfg : MemLp (fun e => f e * g e) 2 ν) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * compensatedProfile N h a b ω : ℝ) : ℂ))
        * (compensatedProduct N f g a b ω : ℂ) ∂P
      = ((b - a : ℝ) : ℂ) ^ 2
          * (∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (f e : ℂ) ∂ν)
          * (∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (g e : ℂ) ∂ν)
        * ∫ ω, Complex.exp (Complex.I * ((u * compensatedProfile N h a b ω : ℝ) : ℂ)) ∂P := by sorry
