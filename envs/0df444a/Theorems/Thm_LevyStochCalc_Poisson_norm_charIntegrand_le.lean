-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_norm_charIntegrand_le
-- name    : LevyStochCalc.Poisson.norm_charIntegrand_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:33:44.90261+00:00
-- url     : https://prove2.me/theorems/935d7bc8-1275-44ab-a1b6-1ad122d08a50
-- title:
--   norm charIntegrand le
-- statement:
--   The source theorem `LevyStochCalc.Poisson.norm_charIntegrand_le` is extracted from `LevyStochCalc.Poisson.CharacterIntegrand`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterIntegrand_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The predictable integrand of the jump chain rule

For a simple integrand carried by a window of finite mark measure the integrand of the jump chain
rule has an exact predictable form: the strictly-past window sum is replaced by its predictable
representative and the deterministic factors are predictable because they are carried by the
window. The integrand is bounded by twice the indicator of the window, so its real and imaginary
parts are admissible for the compensated integral.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Integrand

variable (N : PoissonRandomMeasure P ν)

theorem _root_.LevyStochCalc.Poisson.norm_charIntegrand_le (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ)
    (ω : Ω) (s : ℝ) (e : E) : ‖charIntegrand N w Bfam A T ω s e‖ ≤ 2 := by sorry
