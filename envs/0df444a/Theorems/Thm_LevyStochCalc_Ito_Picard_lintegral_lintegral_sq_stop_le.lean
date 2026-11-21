-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_lintegral_lintegral_sq_stop_le
-- name    : LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_stop_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:15:07.822139+00:00
-- url     : https://prove2.me/theorems/1bfe44f8-7cfa-4a50-8fd8-388603b6ca3c
-- title:
--   lintegral lintegral sq stop le
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_stop_le` is extracted from `LevyStochCalc.Ito.PicardIntegrandBounds`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardIntegrandBounds_F000

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

theorem _root_.LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_stop_le {n : ℕ} {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (Y : SBoundedProcess (n := n) P ℱ T) (hT : 0 ≤ T) (T' : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        ∑ i, (‖Y.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal T' * (bieleckiNorm (P := P) 0 T Y.X) ^ (2 : ℕ) := by sorry
