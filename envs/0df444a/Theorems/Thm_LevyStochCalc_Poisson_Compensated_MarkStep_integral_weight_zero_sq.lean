-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_MarkStep_integral_weight_zero_sq
-- name    : LevyStochCalc.Poisson.Compensated.MarkStep.integral_weight_zero_sq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T12:26:31.342523+00:00
-- url     : https://prove2.me/theorems/bf0adb23-c919-4731-a92f-00d2515fec81
-- title:
--   integral weight zero sq
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.integral_weight_zero_sq` is extracted from `LevyStochCalc.Poisson.MarkStepWeight`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepWeight_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Sums, negations and weightings of mark-step integrands

Two mark-step integrands on a common time grid are added by concatenating their mark
families (`MarkStep.append`), and a mark-step integrand is negated coefficientwise
(`MarkStep.neg`); both operations act additively on the compensated integral and on the
integrand, so the `L²` isometry applies to differences. Multiplying the coefficients from a
given piece on by a bounded measurable weight `w`, and zeroing the earlier ones
(`MarkStep.weight`), yields the isometry for the weighted increment of the integral over a
grid interval.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

section Append

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G G' : MarkStep Ω E ν g)

end Append

section Weight

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν g) {w : Ω → ℝ}
  (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C) (hwm : Measurable w)

include hw hwm in
include hℱ in

theorem _root_.LevyStochCalc.Poisson.Compensated.MarkStep.integral_weight_zero_sq (hG : G.Adapted ℱ) {t : ℝ} (ht : 0 ≤ t)
    (hwa : @StronglyMeasurable Ω ℝ _ (ℱ 0) w) :
    ∫ ω, (w ω * G.integral N t ω) ^ 2 ∂P
      = ∫ ω, (w ω) ^ 2 * (∫ e, ∫ s in Set.Icc (0 : ℝ) t,
          (G.eval s e ω) ^ 2 ∂volume ∂ν) ∂P := by sorry
