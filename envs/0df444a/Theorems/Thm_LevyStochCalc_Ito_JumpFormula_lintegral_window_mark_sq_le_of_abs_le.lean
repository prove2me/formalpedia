-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_lintegral_window_mark_sq_le_of_abs_le
-- name    : LevyStochCalc.Ito.JumpFormula.lintegral_window_mark_sq_le_of_abs_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T10:18:05.488193+00:00
-- url     : https://prove2.me/theorems/7ccfaabd-d378-4bcd-9ea1-1ebf4e355d25
-- title:
--   lintegral window mark sq le of abs le
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.lintegral_window_mark_sq_le_of_abs_le` is extracted from `LevyStochCalc.Ito.ItoLevyMixedBounds`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyMixedBounds_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bounds and admissibility of the mixed integrands

Energy bounds on a bounded window for integrands dominated by finitely many square-integrable
ones, the bounds on the four mixed integrands through the bounded derivatives of the state
function, their continuity in the state, and the progressive measurability of a marked integrand
read at a progressively measurable state.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.lintegral_window_sq_le_of_abs_le`,
  `LevyStochCalc.Ito.JumpFormula.lintegral_window_mark_sq_le_of_abs_le` — energy bounds for
  dominated integrands.
* `LevyStochCalc.Ito.JumpFormula.abs_mixedDriftIntegrand_le`,
  `LevyStochCalc.Ito.JumpFormula.abs_mixedJumpIncrement_le` — bounds on the mixed integrands.
* `LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_time_state_jump` — the triple of
  the time, a progressively measurable state and the jump coefficient along a path is marked
  progressively measurable.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section Norms

end Norms

section Energies

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

omit [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Ito.JumpFormula.lintegral_window_mark_sq_le_of_abs_le {n : ℕ} {φ : Ω → ℝ → E → ℝ}
    {a : Fin n → Ω → ℝ → E → ℝ} {c : ℝ}
    (ha : ∀ i, Measurable fun p : Ω × ℝ × E => a i p.1 p.2.1 p.2.2)
    (h : ∀ ω s e, |φ ω s e| ≤ c * ∑ i, |a i ω s e|) (T : ℝ)
    (hq : ∀ i, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖a i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by sorry
