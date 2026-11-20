-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Solves_lintegral_biSup_sq_driftLeg_lt_top
-- name    : LevyStochCalc.BSDEJ.Solves.lintegral_biSup_sq_driftLeg_lt_top
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T22:25:44.782253+00:00
-- url     : https://prove2.me/theorems/19c43ce4-02d9-49ee-af8f-ab86bad7ec7c
-- title:
--   lintegral biSup sq driftLeg lt top
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Solves.lintegral_biSup_sq_driftLeg_lt_top` is extracted from `LevyStochCalc.BSDEJ.DriftLeg`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_DriftLeg_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The drift leg of a Picard iterate

For a drift `b : Ω → ℝ → ℝ` of finite energy on the horizon `[0, T]` and vanishing off it, the
drift leg is the primitive `t ↦ ∫_{[0, t]} b ω s ds`, restricted to the sample points on which
`b ω` is integrable over `[0, T]` and set to `0` elsewhere. That restriction is a `P`-conull set,
so the drift leg is a version of the raw primitive, and on it every path is the primitive of a
globally integrable function, hence continuous.

## Main definitions

* `LevyStochCalc.BSDEJ.Solves.integrablePaths` — the sample points whose drift path is integrable
  over the horizon.
* `LevyStochCalc.BSDEJ.Solves.driftLeg` — the primitive of the drift, cut to those sample points.

## Main statements

* `driftLeg_ae_eq` — the drift leg is a version of the raw primitive.
* `setIntegral_Icc_eq_intervalIntegral` — the integral over `[0, t]` is the interval integral
  from `0` to `t`, for every real `t`.
* `continuous_driftLeg` — every path of the drift leg is continuous.
* `stronglyAdapted_driftLeg`, `adapted_driftLeg` — the drift leg is adapted to the filtration of
  the drift.
* `adapted_driftLeg_of_rightCont` — the drift leg is adapted to the filtration already when the
  drift is progressive for the right-continuous filtration.
* `measurable_uncurry_driftLeg` — the drift leg is jointly measurable in time and sample point.
* `driftLeg_sub_ae` — the drift leg at the horizon splits at an intermediate time.
* `lintegral_biSup_sq_driftLeg_lt_top` — the drift leg has finite `S²` seminorm.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {b : Ω → ℝ → ℝ} {T : ℝ}

/-! ### The paths on which the drift is integrable -/

/-! ### The drift leg -/

theorem _root_.LevyStochCalc.BSDEJ.Solves.lintegral_biSup_sq_driftLeg_lt_top (hbm : Measurable (Function.uncurry b))
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖driftLeg b T t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by sorry
