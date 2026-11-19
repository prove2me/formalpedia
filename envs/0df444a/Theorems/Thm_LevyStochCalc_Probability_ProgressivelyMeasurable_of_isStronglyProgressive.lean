-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_ProgressivelyMeasurable_of_isStronglyProgressive
-- name    : LevyStochCalc.Probability.ProgressivelyMeasurable.of_isStronglyProgressive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:23:49.98631+00:00
-- url     : https://prove2.me/theorems/3fcb6b55-08e7-4b21-be45-1f721364ddb6
-- title:
--   of isStronglyProgressive
-- statement:
--   The source theorem `LevyStochCalc.Probability.ProgressivelyMeasurable.of_isStronglyProgressive` is extracted from `LevyStochCalc.Probability.Progressive`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

theorem _root_.LevyStochCalc.Probability.ProgressivelyMeasurable.of_isStronglyProgressive (h : IsStronglyProgressive ℱ fun s ω => H ω s) :
    ProgressivelyMeasurable ℱ H := by sorry
