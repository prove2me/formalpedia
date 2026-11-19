-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_ProgressivelyMeasurable_stopped
-- name    : LevyStochCalc.Probability.ProgressivelyMeasurable.stopped
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:29:48.570701+00:00
-- url     : https://prove2.me/theorems/05d94188-76d7-4566-9556-67f33c83613d
-- title:
--   stopped
-- statement:
--   The source theorem `LevyStochCalc.Probability.ProgressivelyMeasurable.stopped` is extracted from `LevyStochCalc.Probability.StoppedProgressive`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_StoppedProgressive_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Stopping a progressively measurable process

Cutting a process off at a stopping time keeps it progressively measurable: before a time `t` the
region `{(ω, s) : s ≤ t, s ≤ τ ω}` is the complement, inside `Ω × (-∞, t]`, of a countable union
of rectangles `{τ ≤ q} × (q, t]` over the rationals, each measurable for the σ-algebra at `t`.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem _root_.LevyStochCalc.Probability.ProgressivelyMeasurable.stopped {ℱ : Filtration ℝ mΩ} {τ : Ω → WithTop ℝ}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) {H : Ω → ℝ → ℝ}
    (hH : ProgressivelyMeasurable ℱ H) :
    ProgressivelyMeasurable ℱ (LevyStochCalc.Probability.stopped τ H) := by sorry
