-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_sq_sum_le_card_sq_mul
-- name    : LevyStochCalc.Probability.sq_sum_le_card_sq_mul
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T14:57:53.949184+00:00
-- url     : https://prove2.me/theorems/98335f39-feb4-45c7-b26d-677a93c992bc
-- title:
--   sq sum le card sq mul
-- statement:
--   The source theorem `LevyStochCalc.Probability.sq_sum_le_card_sq_mul` is extracted from `LevyStochCalc.Probability.DoobContinuous`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Doob's `L²` maximal inequality in continuous time

For a right-continuous martingale on `[0, T]`, the supremum of the paths over the window is
square integrable, with `𝔼[sup_{t ≤ T} |M_t|²] ≤ 4 𝔼[|M_T|²]`.

The discrete inequality is `MeasureTheory.Martingale.eLpNorm_norm_runMax_le`; the passage to
continuous time samples the martingale along the dyadic partition of `[0, T]`, whose points are
increasing in the level, and uses right-continuity to identify the supremum over the window with
the supremum of the sampled maxima.

## Main statements

* `Filtration.compMono`, `martingale_compMono` — sampling along a monotone time map.
* `dyadicTime` — the dyadic partition points of `[0, T]`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Sampling along a monotone time map -/

/-! ### The dyadic partition of `[0, T]` -/

/-! ### The sampled running maxima -/

variable {M : ℝ → Ω → ℝ} {T : ℝ}

/-! ### The supremum over the window -/

/-! ### Doob's `L²` inequality in continuous time -/

/-! ### Bounding the supremum over the window -/

/-! ### Finite sums -/

theorem _root_.LevyStochCalc.Probability.sq_sum_le_card_sq_mul {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ≥0∞) ^ 2 * ∑ i ∈ s, f i ^ 2 := by sorry
