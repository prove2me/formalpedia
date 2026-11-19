-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_ProgressivelyMeasurable_minTime
-- name    : LevyStochCalc.Probability.ProgressivelyMeasurable.minTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:23:18.285913+00:00
-- url     : https://prove2.me/theorems/23ac7f3f-44ad-4ac5-9a84-f8b68cebeab0
-- title:
--   minTime
-- statement:
--   The source theorem `LevyStochCalc.Probability.ProgressivelyMeasurable.minTime` is extracted from `LevyStochCalc.Probability.Progressive`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_Progressive_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Progressively measurable real processes

`ProgressivelyMeasurable ℱ H` says that the process `H : Ω → ℝ → E`, viewed as a function of
`(ω, s)`, is `ℱ t ⊗ Borel`-measurable on the time window `s ≤ t`, for every `t`. This is
the progressive measurability of Mathlib's `IsStronglyProgressive`, phrased on `Ω × ℝ` by
truncating the time variable at `t`, which is the form in which the stochastic integrals of
this library consume it; `isStronglyProgressive` and `of_isStronglyProgressive` relate the
two.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω}

section General

variable [TopologicalSpace E] [Zero E] [TopologicalSpace F] [Zero F]

namespace ProgressivelyMeasurable

variable {ℱ : Filtration ℝ mΩ} {H : Ω → ℝ → E}

theorem _root_.LevyStochCalc.Probability.ProgressivelyMeasurable.minTime (h : ProgressivelyMeasurable ℱ H) (T : ℝ) :
    ProgressivelyMeasurable ℱ fun ω s => H ω (min s T) := by sorry
