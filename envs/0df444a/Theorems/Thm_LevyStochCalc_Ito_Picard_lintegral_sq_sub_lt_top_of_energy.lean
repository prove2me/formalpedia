-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_lintegral_sq_sub_lt_top_of_energy
-- name    : LevyStochCalc.Ito.Picard.lintegral_sq_sub_lt_top_of_energy
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T22:03:11.527432+00:00
-- url     : https://prove2.me/theorems/ecb3bda6-dfab-4b70-a152-a9aebde30d06
-- title:
--   lintegral sq sub lt top of energy
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.lintegral_sq_sub_lt_top_of_energy` is extracted from `LevyStochCalc.Ito.PicardContractionEstimate`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F000
import Definitions.Def_LevyStochCalc_Ito_PicardIntegrandBounds_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Picard contraction estimate

The contraction estimate of `bieleckiNorm_picardStep_diff_le` is stated for the Picard step along
two raw path maps. Along two processes of the space its hypotheses are supplied by the frozen
integrand lemmas, and the Bielecki norm of a difference is unchanged by freezing at the horizon, so
the estimate transfers to `picardStepOnStop`, from there through the modification
`picardSelfMap_ae_eq` to `picardSelfMap` itself, and in the same way to the step taken against a
raw state process. The iterates `picardIter` of the self-map are consequently geometrically
Bielecki-Cauchy, and at a weight making the contraction rate `< 1` they converge to
`bieleckiLimit`.

## Main statements

* `bieleckiNorm_picardStepOnStop_diff_le` — the estimate for the step along frozen processes.
* `bieleckiNorm_picardSelfMap_diff_le` — the estimate for the self-map.
* `bieleckiNorm_picardIter_sub_bieleckiLimit_le` — the iterates converge to `bieleckiLimit`.
* `bieleckiNorm_picardStepOnStop_sub_rawStop_le` — the estimate against a raw state process.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

/-! ### The difference of two frozen processes -/

omit [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Ito.Picard.lintegral_sq_sub_lt_top_of_energy {Z₁ Z₂ : ℝ → Ω → (Fin n → ℝ)}
    (hm₁ : Measurable (Function.uncurry Z₁)) (hm₂ : Measurable (Function.uncurry Z₂))
    (h₁ : ∀ b : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h₂ : ∀ b : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (b : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖Z₁ s ω - Z₂ s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by sorry
