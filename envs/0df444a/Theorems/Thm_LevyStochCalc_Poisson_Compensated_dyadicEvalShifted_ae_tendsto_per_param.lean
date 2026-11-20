-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_dyadicEvalShifted_ae_tendsto_per_param
-- name    : LevyStochCalc.Poisson.Compensated.dyadicEvalShifted_ae_tendsto_per_param
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T20:01:37.925912+00:00
-- url     : https://prove2.me/theorems/b219ae26-56e2-4525-bf3c-bbbbe1f8390d
-- title:
--   dyadicEvalShifted ae tendsto per param
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.dyadicEvalShifted_ae_tendsto_per_param` is extracted from `LevyStochCalc.Poisson.CompensatedDensityShifted`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityShifted_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The adapted (left-shifted) dyadic eval

The variant of the dyadic evaluation whose coefficient on the `i`-th dyadic interval is the
average of `φ` over the *previous* interval, hence `ℱ_{tᵢ}`-measurable for progressively
measurable `φ`. Its almost-everywhere and `L²(P ⊗ ds ⊗ ν)` convergence to `φ` follow from the
same Lebesgue-density and dominated-convergence arguments, the left shift contributing a
vanishing displacement.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Adapted (left-shifted) eval

The coefficient on the `i`-th dyadic interval is the average over the *previous*
interval (`dyadicAvg_shifted`), making it `ℱ_{tᵢ}`-measurable for progressively
measurable `φ` — the predictable/adapted version of `dyadicEval`. -/

theorem _root_.LevyStochCalc.Poisson.Compensated.dyadicEvalShifted_ae_tendsto_per_param
    {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M) (ω : Ω) (e : E) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun n => dyadicEvalShifted T φ n s ω e) Filter.atTop (nhds (φ ω s e)) := by sorry
