-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_markedProgressivelyMeasurable_comp_state
-- name    : LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_comp_state
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:35:56.376178+00:00
-- url     : https://prove2.me/theorems/c65758ef-01b5-47d6-8def-9f58953fb410
-- title:
--   markedProgressivelyMeasurable comp state
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_comp_state` is extracted from `LevyStochCalc.Ito.PicardIntegrandBounds`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardIntegrandBounds_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Square integrability of the Picard integrands along a state process

Linear growth of the coefficients, read off the Lipschitz hypothesis by comparison with the
state `0`, turns the bounds at that single state recorded by `IsRegular` into bounds along a
state process: whenever the state has finite energy over every horizon, the drift, diffusion
and jump integrands evaluated along it are square integrable at every horizon, and a member of
the process space frozen at `T` has that energy. Composing a jointly measurable coefficient
with a measurable, respectively progressively measurable, state process supplies the matching
measurability of the integrands.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

theorem _root_.LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_comp_state {n : ℕ}
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {X : ℝ → Ω → (Fin n → ℝ)}
    (hX : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ (fun ω s => X s ω i))
    {g : ℝ → (Fin n → ℝ) → E → ℝ}
    (hg : Measurable fun p : ℝ × (Fin n → ℝ) × E => g p.1 p.2.1 p.2.2) :
    Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => g s (X s ω) e) := by sorry
