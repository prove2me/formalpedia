-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_SecondMoment_setIntegral_exp_mul_setIntegral
-- name    : LevyStochCalc.Ito.SecondMoment.setIntegral_exp_mul_setIntegral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T07:25:58.820745+00:00
-- url     : https://prove2.me/theorems/0a5a3d3a-7753-4594-b70a-604a8fabf984
-- title:
--   setIntegral exp mul setIntegral
-- statement:
--   The source theorem `LevyStochCalc.Ito.SecondMoment.setIntegral_exp_mul_setIntegral` is extracted from `LevyStochCalc.Ito.SecondMomentWeighted`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_SecondMomentWeighted_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The exponentially weighted second moment of an Itô–Lévy process

The map `t ↦ 𝔼[X_t²]` is the initial value plus the time integral of the rate
`2 𝔼[X_s b_s] + ∑_j 𝔼[σ_j(s)²] + 𝔼 ∫_E γ(s, e)² ν(de)`, so integration by parts against the
weight `e^{βs}` gives

`e^{βT} 𝔼[X_T²] = 𝔼[X₀²] + ∫_0^T e^{βs} (β 𝔼[X_s²] + 2 𝔼[X_s b_s] + ∑_j 𝔼[σ_j(s)²]
  + 𝔼 ∫_E γ(s, e)² ν(de)) ds`,

the form in which the a-priori estimates for BSDEs with jumps read the quadratic formula. The
weighting of an absolutely continuous function by an exponential is isolated first, as a real
identity. The vector form follows coordinatewise, and the cross witness carried by the driver
gives the bilinear and the weighted forms over its augmented joint natural filtration.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Weight

/-! ### The exponential weight: integration by parts against `e^{βs}` -/

theorem _root_.LevyStochCalc.Ito.SecondMoment.setIntegral_exp_mul_setIntegral {g : ℝ → ℝ} {T : ℝ}
    (hg : IntegrableOn g (Set.Icc (0 : ℝ) T)) (β : ℝ) :
    ∫ s in Set.Icc (0 : ℝ) T, β * Real.exp (β * s) * ∫ r in Set.Icc (0 : ℝ) s, g r
      = Real.exp (β * T) * (∫ r in Set.Icc (0 : ℝ) T, g r)
        - ∫ r in Set.Icc (0 : ℝ) T, Real.exp (β * r) * g r := by sorry
