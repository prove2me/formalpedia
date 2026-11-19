-- Prove2me | Theorems.Thm_LevyStochCalc_integral_abs_add_four_le
-- name    : LevyStochCalc.integral_abs_add_four_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:47:18.486193+00:00
-- url     : https://prove2.me/theorems/5dbecf3d-17bd-4afd-b0aa-f8cffdb84e3b
-- title:
--   integral abs add four le
-- statement:
--   The source theorem `LevyStochCalc.integral_abs_add_four_le` is extracted from `LevyStochCalc.Probability.AbsMoment`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_AbsMoment_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# First absolute moment from a second-moment bound

On a probability space the first absolute moment of a real random variable is bounded by the
square root of its second moment.

## Main statements

* `LevyStochCalc.integral_abs_le_sqrt_of_integral_sq_le` — `𝔼|f| ≤ √V` whenever `𝔼f² ≤ V`.
* `LevyStochCalc.integral_abs_le_of_bounded` — `𝔼|f| ≤ K` for `|f| ≤ K`.
* `LevyStochCalc.integral_abs_add_four_le` — the triangle inequality for four summands.
-/

namespace LevyStochCalc

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.integral_abs_add_four_le {P : Measure Ω} [IsProbabilityMeasure P]
    {a b c d : Ω → ℝ} (ha : Integrable a P) (hb : Integrable b P) (hc : Integrable c P)
    (hd : Integrable d P) {A B C D : ℝ} (hA : ∫ ω, |a ω| ∂P ≤ A)
    (hB : ∫ ω, |b ω| ∂P ≤ B) (hC : ∫ ω, |c ω| ∂P ≤ C) (hD : ∫ ω, |d ω| ∂P ≤ D) :
    ∫ ω, |a ω + b ω + c ω + d ω| ∂P ≤ A + B + C + D := by sorry
