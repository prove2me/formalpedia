-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_triple_ofReal_integral_eq_lintegral
-- name    : LevyStochCalc.Poisson.Compensated.triple_ofReal_integral_eq_lintegral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T09:56:53.510573+00:00
-- url     : https://prove2.me/theorems/ef587bff-a79c-4b54-94ed-92f63dccbba4
-- title:
--   triple ofReal integral eq lintegral
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.triple_ofReal_integral_eq_lintegral` is extracted from `LevyStochCalc.Poisson.CompensatedDensityLimit`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityLimit_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cross-resolution Cauchy estimate and the `L²` limit

The isometry for the difference of two step integrals at different dyadic resolutions, the
resulting Cauchy estimate for the Euler sums of a bounded predictable integrand, and the limit
in `L²(P)` it produces. Closing bricks on the regularity of monotone `ℝ≥0∞`-valued functions of
time and the right-continuity of the intensity of shrinking time-mark boxes support the path
regularity of that limit.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

theorem _root_.LevyStochCalc.Poisson.Compensated.triple_ofReal_integral_eq_lintegral
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (h : Ω → ℝ → E → ℝ) (hmeas : Measurable (fun p : Ω × ℝ × E => h p.1 p.2.1 p.2.2))
    {C : ℝ} (hC : ∀ ω s e, |h ω s e| ≤ C) {S : Set E} (hS : MeasurableSet S) (hSfin : ν S ≠ ⊤)
    (hsupp : ∀ ω s e, e ∉ S → h ω s e = 0) :
    ENNReal.ofReal (∫ ω, ∫ e, ∫ s in Set.Icc (0 : ℝ) T, (h ω s e) ^ 2 ∂volume ∂ν ∂P)
      = ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖h ω s e‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P := by sorry
