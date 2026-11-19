-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_ProgressivelyMeasurable_isStronglyProgressive
-- name    : LevyStochCalc.Probability.ProgressivelyMeasurable.isStronglyProgressive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:23:33.705197+00:00
-- url     : https://prove2.me/theorems/8dd15583-d9d4-4a51-84ab-354d9198f84d
-- title:
--   isStronglyProgressive
-- statement:
--   The source theorem `LevyStochCalc.Probability.ProgressivelyMeasurable.isStronglyProgressive` is extracted from `LevyStochCalc.Probability.Progressive`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

theorem _root_.LevyStochCalc.Probability.ProgressivelyMeasurable.isStronglyProgressive (h : ProgressivelyMeasurable ℱ H) :
    IsStronglyProgressive ℱ fun s ω => H ω s := by sorry
