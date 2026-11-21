-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_ae_eq_of_tendsto_stepIntegral
-- name    : LevyStochCalc.Poisson.ae_eq_of_tendsto_stepIntegral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T15:18:41.583771+00:00
-- url     : https://prove2.me/theorems/c41d87dc-aab3-4b75-930b-65c8ca702afe
-- title:
--   ae eq of tendsto stepIntegral
-- statement:
--   The source theorem `LevyStochCalc.Poisson.ae_eq_of_tendsto_stepIntegral` is extracted from `LevyStochCalc.Poisson.CompensatedProfile`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfile_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral of a deterministic mark profile over a step

The compensated step integrals of simple mark profiles obey the isometry
`‖J(f) − J(g)‖_{L²(P)} = √(b − a) ‖f − g‖_{L²(ν)}`, so an `L²(P)` limit of the compensated step
integrals of simple profiles converging in `L²(ν)` is determined, up to a null set, by the limit
profile alone. That limit is the compensated integral over the step `(a, b]` of a
square-integrable deterministic mark profile `f : E → ℝ` against a Poisson random measure with
intensity `ν`. It agrees with the compensated step integral at a simple profile and carries the
Lévy character

  `E[exp (i u J(f))] = exp ((b − a) ∫ (exp (i u f) − 1 − i u f) dν)`.

## Main definitions

* `LevyStochCalc.Poisson.IsCompensatedProfile` — being a strongly measurable `L²(P)` limit at a
  step of the compensated step integrals of every sequence of simple mark profiles converging to
  a mark profile in `L²(ν)`.
* `LevyStochCalc.Poisson.compensatedProfile` — the compensated integral of a square-integrable
  deterministic mark profile over a step.

## Main statements

* `LevyStochCalc.Poisson.ae_eq_of_tendsto_stepIntegral` — an `L²(P)` limit of the compensated
  step integrals of simple profiles converging in `L²(ν)` depends only on the limit profile.
* `LevyStochCalc.Poisson.stronglyMeasurable_compensatedProfile`,
  `LevyStochCalc.Poisson.memLp_compensatedProfile` — measurability and square integrability.
* `LevyStochCalc.Poisson.tendsto_stepIntegral_compensatedProfile` — the compensated step
  integrals of simple profiles converging to a profile in `L²(ν)` converge to its compensated
  integral in `L²(P)`.
* `LevyStochCalc.Poisson.compensatedProfile_toFun` — agreement with the compensated step
  integral at a simple mark profile.
* `LevyStochCalc.Poisson.integral_exp_I_mul_compensatedProfile` — the Lévy character of the
  compensated integral of a mark profile over a step.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Independence of the approximating sequence -/

theorem _root_.LevyStochCalc.Poisson.ae_eq_of_tendsto_stepIntegral (N : PoissonRandomMeasure P ν)
    {G G' : ℕ → SimpleProfile E ν} {f : E → ℝ} (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) {J J' : Ω → ℝ} (hJ : MemLp J 2 P) (hJ' : MemLp J' 2 P)
    (hG : Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν) atTop (nhds 0))
    (hG' : Tendsto (fun n => eLpNorm (fun e => (G' n).toFun e - f e) 2 ν) atTop (nhds 0))
    (hJlim : Tendsto (fun n => eLpNorm (fun ω => (G n).stepIntegral N a b ω - J ω) 2 P)
      atTop (nhds 0))
    (hJ'lim : Tendsto (fun n => eLpNorm (fun ω => (G' n).stepIntegral N a b ω - J' ω) 2 P)
      atTop (nhds 0)) :
    J =ᵐ[P] J' := by sorry
