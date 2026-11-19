-- Prove2me | Theorems.Thm_LevyStochCalc_abs_setIntegral_Ioc_le
-- name    : LevyStochCalc.abs_setIntegral_Ioc_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:41:48.060713+00:00
-- url     : https://prove2.me/theorems/33633648-a51a-40b8-8468-238581ac7516
-- title:
--   abs setIntegral Ioc le
-- statement:
--   The source theorem `LevyStochCalc.abs_setIntegral_Ioc_le` is extracted from `LevyStochCalc.Brownian.DriftIncrement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_DriftIncrement_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Increments of the integral of a bounded function

The drift part of an Itô process is `t ↦ ∫_0^t b_s ds`. Its increment across a cell is the
integral over that cell, and is bounded by the bound on `b` times the cell length.

## Main statements

* `LevyStochCalc.integrableOn_of_bounded_of_measurable` — a bounded measurable function is
  integrable on any set of finite measure.
* `LevyStochCalc.setIntegral_Icc_sub_Icc` — `∫_{[0,b]} − ∫_{[0,a]} = ∫_{(a,b]}`.
* `LevyStochCalc.abs_setIntegral_Ioc_le` — `|∫_{(a,b]} f| ≤ B·(b − a)`.
* `LevyStochCalc.abs_setIntegral_Icc_sub_le` — `t ↦ ∫_{[0,t]} f` is `B`-Lipschitz.
* `LevyStochCalc.continuous_setIntegral_Icc` — hence continuous.
* `LevyStochCalc.measurable_setIntegral` — the integral over a fixed set is measurable in
  the parameter.
* `LevyStochCalc.measurable_setIntegral_Ioc` — the window integral is measurable in the
  parameter.
-/

namespace LevyStochCalc

open MeasureTheory

theorem _root_.LevyStochCalc.abs_setIntegral_Ioc_le {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {a b : ℝ} (hab : a ≤ b) :
    |∫ s in Set.Ioc a b, f s ∂volume| ≤ B * (b - a) := by sorry
