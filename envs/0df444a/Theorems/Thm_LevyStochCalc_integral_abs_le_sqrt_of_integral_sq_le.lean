-- Prove2me | Theorems.Thm_LevyStochCalc_integral_abs_le_sqrt_of_integral_sq_le
-- name    : LevyStochCalc.integral_abs_le_sqrt_of_integral_sq_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:46:55.916101+00:00
-- url     : https://prove2.me/theorems/e7ba39a4-3659-42f4-a1e7-90a161173f5f
-- title:
--   integral abs le sqrt of integral sq le
-- statement:
--   The source theorem `LevyStochCalc.integral_abs_le_sqrt_of_integral_sq_le` is extracted from `LevyStochCalc.Probability.AbsMoment`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

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

theorem _root_.LevyStochCalc.integral_abs_le_sqrt_of_integral_sq_le {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf : Integrable (fun ω => |f ω|) P)
    (hf2 : Integrable (fun ω => f ω ^ 2) P) {V : ℝ} (hV : ∫ ω, f ω ^ 2 ∂P ≤ V) :
    ∫ ω, |f ω| ∂P ≤ Real.sqrt V := by sorry
