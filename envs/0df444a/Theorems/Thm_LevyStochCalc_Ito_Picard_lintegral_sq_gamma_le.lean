-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_lintegral_sq_gamma_le
-- name    : LevyStochCalc.Ito.Picard.lintegral_sq_gamma_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:31:50.548308+00:00
-- url     : https://prove2.me/theorems/7f7e768f-6f78-49a0-8082-d25fde0e32e6
-- title:
--   lintegral sq gamma le
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.lintegral_sq_gamma_le` is extracted from `LevyStochCalc.Ito.PicardIntegrandBounds`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardIntegrandBounds_F001

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

theorem _root_.LevyStochCalc.Ito.Picard.lintegral_sq_gamma_le {n d : ℕ} {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν) {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (s : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    ∫⁻ e, (‖coeffs.γ s x e i‖₊ : ℝ≥0∞) ^ 2 ∂ν
      ≤ 2 * (∫⁻ e, (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
        + ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖x i'‖₊ : ℝ≥0∞) ^ 2 := by sorry
