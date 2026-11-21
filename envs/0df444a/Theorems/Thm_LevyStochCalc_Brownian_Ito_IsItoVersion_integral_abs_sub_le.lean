-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsItoVersion_integral_abs_sub_le
-- name    : LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sub_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:20:36.669192+00:00
-- url     : https://prove2.me/theorems/89be5529-3144-4365-add3-acfa834cbb34
-- title:
--   integral abs sub le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sub_le` is extracted from `LevyStochCalc.Brownian.ItoProcessVersion`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoProcessVersion_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Continuous adapted versions of an Itô process

The Itô integral is defined time by time, so the process `t ↦ X_t` it produces has no path
regularity built in. `IsItoVersion` names a continuous adapted process agreeing with the Itô
process at each time; such a version has jointly measurable paths, so it can be composed with a
continuous function and fed back into a time integral or an Itô integral.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsItoVersion` — a continuous adapted version of an Itô process.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.measurable_uncurry` — its joint measurability.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.progressivelyMeasurable_comp` — a continuous function
  of it is progressively measurable.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.sub_ae` — its increment splits into drift and
  martingale parts.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sub_le` and
  `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_sq_sub_le` — the increment moments carried
  over from `itoProcess`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Version

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

variable {W ℱ hℱ H hm hp hq} {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}

section Moments

variable {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hC0 hCH in

theorem _root_.LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sub_le (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    MeasureTheory.Integrable (fun ω : Ω => |X v ω - X u ω|) P
      ∧ ∫ ω, |X v ω - X u ω| ∂P ≤ B * (v - u) + C * Real.sqrt (v - u) := by sorry
