-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_lintegral_sq_sub_bieleckiLimit_rpow_le
-- name    : LevyStochCalc.Ito.Picard.lintegral_sq_sub_bieleckiLimit_rpow_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:36:17.426778+00:00
-- url     : https://prove2.me/theorems/1ec9f345-08c2-49f2-9462-cf83e87a4073
-- title:
--   lintegral sq sub bieleckiLimit rpow le
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.lintegral_sq_sub_bieleckiLimit_rpow_le` is extracted from `LevyStochCalc.Ito.PicardLimit`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardLimit_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Limits of Bielecki-Cauchy sequences of path maps

A sequence of path maps whose consecutive Bielecki differences are summable converges: at every
time of the window the increments are summable in `L²`, hence almost surely absolutely summable,
so the pointwise `limsup` is the almost-sure limit. The `limsup` inherits joint measurability and
progressive measurability from the sequence, and the Bielecki distance to the sequence tends to
zero.

The Bielecki norm is the weighted supremum over `t` of the `L²` norms, so it controls the paths
at each fixed time only: a càdlàg property of the terms is not inherited by the limit. The limit
constructed here is therefore a jointly measurable, progressively measurable path map, not an
`SBoundedProcess`; the càdlàg property of a Picard fixed point comes from the Picard step's own
output, not from the limit.

## Main statements

* `bieleckiLimit` — the pointwise `limsup` of a sequence of path maps.
* `measurable_bieleckiLimit`, `progressivelyMeasurable_bieleckiLimit` — its measurability.
* `bieleckiNorm_le_of_perTime_rpow`, `lintegral_sq_rpow_le_of_bieleckiNorm` — the two directions
  between the Bielecki norm and the weighted `L²` norms at a fixed time.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.Picard

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The Bielecki norm and the weighted `L²` norms at a fixed time -/

/-! ### The limit path map -/

/-! ### Telescoping -/

/-! ### Almost sure convergence at a fixed time -/

/-! ### Convergence to the limit path map -/

theorem _root_.LevyStochCalc.Ito.Picard.lintegral_sq_sub_bieleckiLimit_rpow_le (β T : ℝ) {X : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hmeas : ∀ k, Measurable (Function.uncurry (X k))) {c : ℕ → ℝ≥0∞}
    (hstep : ∀ k, bieleckiNorm (P := P) β T (fun t ω i => X (k + 1) t ω i - X k t ω i) ≤ c k)
    (hc : ∑' k, c k ≠ ⊤) (k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫⁻ ω, ∑ i, (‖X k t ω i - bieleckiLimit X t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      ≤ ENNReal.ofReal (Real.exp (β * t)) * ∑' j, c (k + j) := by sorry
