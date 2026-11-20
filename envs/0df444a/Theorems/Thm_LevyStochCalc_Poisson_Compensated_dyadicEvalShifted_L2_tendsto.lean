-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_dyadicEvalShifted_L2_tendsto
-- name    : LevyStochCalc.Poisson.Compensated.dyadicEvalShifted_L2_tendsto
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T20:54:35.679178+00:00
-- url     : https://prove2.me/theorems/614eac97-a846-4513-8d27-c12378a3b45e
-- title:
--   dyadicEvalShifted L2 tendsto
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.dyadicEvalShifted_L2_tendsto` is extracted from `LevyStochCalc.Poisson.CompensatedDensityShifted`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityShifted_F001

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

set_option maxHeartbeats 1000000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.

theorem _root_.LevyStochCalc.Poisson.Compensated.dyadicEvalShifted_L2_tendsto
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν] {T : ℝ} (hT : 0 < T)
    (φ : Ω → ℝ → E → ℝ) (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M)
    {S : Set E} (hS_meas : MeasurableSet S) (hS_fin : ν S ≠ ⊤)
    (hSupp : ∀ ω e, e ∉ S → ∀ u, φ ω u e = 0) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      Filter.atTop (nhds 0) := by sorry
