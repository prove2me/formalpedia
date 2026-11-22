-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_markedProgressivelyMeasurable_time_state_jump
-- name    : LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_time_state_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T12:37:09.000169+00:00
-- url     : https://prove2.me/theorems/4a278364-c810-421d-be29-9234613a5d72
-- title:
--   markedProgressivelyMeasurable time state jump
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_time_state_jump` is extracted from `LevyStochCalc.Ito.ItoLevyMixedBounds`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyMixedBounds_F001

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

end Energies

section MixedBounds

variable {n d : ℕ} {E : Type v} {u : ℝ → (Fin n → ℝ) → ℝ}

end MixedBounds

section MixedContinuity

variable {n d : ℕ} {E : Type v} {u : ℝ → (Fin n → ℝ) → ℝ} {z : ℕ → Fin n → ℝ} {w : Fin n → ℝ}

end MixedContinuity

section Progressive

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

theorem _root_.LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_time_state_jump {n d : ℕ}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {coeffs : JumpDiffusionCoeffs n d E}
    {Xp Y : ℝ → Ω → (Fin n → ℝ)}
    (hY : ∀ i, ProgressivelyMeasurable ℱ fun ω s => Y s ω i)
    (hγ : ∀ i, MarkedProgressivelyMeasurable ℱ (SmallJump.pathJumpCoeff coeffs Xp i)) :
    MarkedProgressivelyMeasurable ℱ fun ω s e =>
      ((s, Y s ω, coeffs.γ s (Xp s ω) e) : ℝ × (Fin n → ℝ) × (Fin n → ℝ)) := by sorry
