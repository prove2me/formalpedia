-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsItoVersion_lintegral_window_abs_sub_le
-- name    : LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_window_abs_sub_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:19:25.060008+00:00
-- url     : https://prove2.me/theorems/72dfcd64-435c-4a39-adc5-7d79af57b4e3
-- title:
--   lintegral window abs sub le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_window_abs_sub_le` is extracted from `LevyStochCalc.Brownian.ItoProcessWindow`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoProcessVersion_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Window averages of an Itô process's increments

Freezing a continuous version of an Itô process at the left endpoint of a window and integrating
the resulting displacement over the window and the sample space gives a bound of order
`(v − u)·√(v − u)`, which is what makes the grid Riemann sums of the Itô formula converge.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_window_abs_sub_le` — the `L¹` window bound.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_window_sq_sub_le` — the `L²` window bound.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Window

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {H : Ω → ℝ → ℝ} {hm : Measurable (Function.uncurry H)}
  {hp : Probability.ProgressivelyMeasurable ℱ H}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hC0 hCH in

theorem _root_.LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_window_abs_sub_le
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    ∫⁻ ω, ∫⁻ s in Set.Ioc u v, ENNReal.ofReal |X s ω - X u ω| ∂volume ∂P
      ≤ ENNReal.ofReal ((v - u) * (B * (v - u) + C * Real.sqrt (v - u))) := by sorry
