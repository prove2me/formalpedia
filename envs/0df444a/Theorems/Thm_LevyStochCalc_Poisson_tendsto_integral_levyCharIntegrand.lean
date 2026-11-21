-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_tendsto_integral_levyCharIntegrand
-- name    : LevyStochCalc.Poisson.tendsto_integral_levyCharIntegrand
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T15:17:01.176438+00:00
-- url     : https://prove2.me/theorems/551ea2a2-d759-475a-aac6-c366f6f385ec
-- title:
--   tendsto integral levyCharIntegrand
-- statement:
--   The source theorem `LevyStochCalc.Poisson.tendsto_integral_levyCharIntegrand` is extracted from `LevyStochCalc.Poisson.ProfileCharacter`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ProfileCharacter_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The character of a compensated step integral of a mark profile

The count of a Poisson random measure on a region of finite intensity is Poisson, so the
character of the compensated count carries the Lévy–Khintchine integrand `e^{iuc} - 1 - iuc`
at the coefficient `c`. A simple mark profile pairs pairwise-disjoint mark sets with constant
coefficients, so over a step its compensated integral is a sum of independent compensated
counts and its character is the product of the counts' characters,

  `E[exp (i u J(f))] = exp ((b - a) ∫ (exp (i u f) - 1 - i u f) dν)`.

The right-hand side is continuous along `L²(ν)` convergence of the profile, so the identity
transfers to a profile approximated by simple ones together with any `L²(P)` limit of their
compensated step integrals.

## Main definitions

* `LevyStochCalc.Poisson.levyCharIntegrand` — the integrand `e^{iux} - 1 - iux`.

## Main statements

* `LevyStochCalc.Poisson.integral_exp_I_mul_compensated` — the character of a compensated
  count on a region of finite intensity.
* `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_stepIntegral` — the character of the
  compensated step integral of a simple mark profile.
* `LevyStochCalc.Poisson.integrable_levyCharIntegrand` — integrability of the integrand at a
  square-integrable mark profile.
* `LevyStochCalc.Poisson.tendsto_integral_levyCharIntegrand` — continuity of the Lévy
  characteristic exponent along `L²(ν)` convergence of the profile.
* `LevyStochCalc.Poisson.integral_exp_I_mul_of_tendsto_stepIntegral` — the character of an
  `L²(P)` limit of the compensated step integrals of simple profiles converging in `L²(ν)`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The Lévy–Khintchine integrand -/

/-! ### The character of a count and of a compensated count -/

/-! ### The character at a simple mark profile -/

namespace SimpleProfile

end SimpleProfile

/-! ### Passage to a general square-integrable profile -/

omit [SigmaFinite ν] in

theorem _root_.LevyStochCalc.Poisson.tendsto_integral_levyCharIntegrand (u : ℝ) {g : ℕ → E → ℝ} {f : E → ℝ}
    (hg : ∀ n, MemLp (g n) 2 ν) (hf : MemLp f 2 ν)
    (hconv : Tendsto (fun n => eLpNorm (fun e => g n e - f e) 2 ν) atTop (nhds 0)) :
    Tendsto (fun n => ∫ e, levyCharIntegrand u (g n e) ∂ν) atTop
      (nhds (∫ e, levyCharIntegrand u (f e) ∂ν)) := by sorry
