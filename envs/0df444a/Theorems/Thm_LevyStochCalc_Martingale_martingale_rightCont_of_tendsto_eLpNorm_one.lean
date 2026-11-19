-- Prove2me | Theorems.Thm_LevyStochCalc_Martingale_martingale_rightCont_of_tendsto_eLpNorm_one
-- name    : LevyStochCalc.Martingale.martingale_rightCont_of_tendsto_eLpNorm_one
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T22:17:55.151976+00:00
-- url     : https://prove2.me/theorems/745c20a0-9934-4213-9511-f026f17a1169
-- title:
--   martingale rightCont of tendsto eLpNorm one
-- statement:
--   The source theorem `LevyStochCalc.Martingale.martingale_rightCont_of_tendsto_eLpNorm_one` is extracted from `LevyStochCalc.Martingale.RightCont`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Martingale.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Martingales on the right-continuation of a filtration

An `ℱ`-martingale on `ℝ` whose time slices are right-continuous in `L¹` is a martingale on
the right-continuation `ℱ₊` of `ℱ`, `ℱ₊ s = ⨅ r > s, ℱ r` (no null sets are added): an
`ℱ₊ s`-measurable set lies in every `ℱ r` with `r > s`, so the martingale identity holds on it
from every later time, and right-`L¹`-continuity carries it down to `s`.
-/

open MeasureTheory Filter Topology

namespace LevyStochCalc.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {F : ℝ → Ω → ℝ}

theorem _root_.LevyStochCalc.Martingale.martingale_rightCont_of_tendsto_eLpNorm_one (hmart : Martingale F ℱ P)
    (hrc : ∀ s : ℝ, Tendsto (fun r => eLpNorm (F r - F s) 1 P) (𝓝[>] s) (𝓝 0)) :
    Martingale F ℱ.rightCont P := by sorry
