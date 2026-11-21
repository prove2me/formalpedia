-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_lintegral_sq_sigma_lt_top_of_energy
-- name    : LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_energy
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:08:44.5848+00:00
-- url     : https://prove2.me/theorems/8a7a6d68-b9af-45a6-bfca-1c63c7595bf3
-- title:
--   lintegral sq sigma lt top of energy
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_energy` is extracted from `LevyStochCalc.Ito.PicardIntegrandBounds`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiContractionTight_F000
import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiContraction_F000
import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiNorm_F001
import Definitions.Def_LevyStochCalc_Ito_PicardSelfMap_F000
import Definitions.Def_LevyStochCalc_Ito_PicardStepMap_F000
import Definitions.Def_LevyStochCalc_Ito_PicardStepMap_F001
import Definitions.Def_LevyStochCalc_Ito_PicardStochasticLipschitz_F000
import Mathlib.Algebra.Order.Chebyshev

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

theorem _root_.LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_energy {n d : ℕ} {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZsq : ∀ b : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) (j : Fin d) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.σ s (Z s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by sorry
